# Agda Supplement for *Context-Free Session Types with Borrowing*

This directory contains the Agda formalization accompanying the paper. It
defines the CSTB calculus, its declarative and algorithmic type systems, typed
high-level processes, untyped low-level processes and the metatheoretic results.

## Software requirements

- [Agda 2.8.0](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html)
- [Agda standard library 2.4](https://wiki.portal.chalmers.se/agda/Libraries/StandardLibrary)

We provide a Dockerfile that builds an image with the required versions of Agda
and the standard library. From inside the directory containing this README.md run

```sh
docker build . -t borrowed-cf/agda
```

To enter a shell in an ephemeral container run

```sh
docker run --rm -it borrowed-cf/agda
```


## System requirements

Checking the supplement can require significant amounts of memory. For a clean
build we observed memory usage up to 20-25GB. When using Docker, ensure that the
VM has sufficient memory available.

## Building

Due to the amount of proof code checking the full supplement, as well as select
modules (ie. safety and simulation results) can take significant time (30-40
min) and memory (20-25GB), especially for a clean build.

Selected modules can be checked by, e.g.,

```sh
agda BorrowedCF/Algorithmic.agda
```

## Structure

```
BorrowedCF/
│
├── Prelude.agda, FinKits.agda, Kits.agda
│   Shared notation and generic de Bruijn renaming/substitution machinery.
│
├── Types/ and Types.agda
│   Type syntax, equivalence, the various type predicates, and
│   substitutions for the algorithmic system.
│
├── Terms/ and Terms.agda
│   Expression syntax, declarative typing, and substitution support.
│
├── Context/ and Context.agda
│   Structural contexts, joins, equivalence, subcontexts, and constraints.
│
├── Processes/
│   Typed processes, tree and soup run times, and both translations.
│
├── Reduction/
│   Expression and process reductions for the typed and untyped calculi.
│
├── Algorithmic.agda and Algorithmic/
│   Algorithmic type system, soundness proof.
│
├── Completeness/
│   Completeness proof of the algorithmic system.
│
├── Safety/
│   Progress and preservation for high-level processes.
│
└── Simulation/
    Forward and backward operational correspondence
	between high- and low-level processes.
```

## Main results

### Definitions

For the definitions in the paper and the appendix we list the corresponding Agda definitions.

| Definition       | Location in the paper | Agda definition |
|------------------|-----------------------|-----------------|
| Type syntax               | Fig. 4    | `BorrowedCF.Types.Syntax.⊢_` |
| Expression syntax         | Fig. 4    | `BorrowedCF.Terms.Base.Tm` |
| Typed process syntax      | Fig. 4    | `BorrowedCF.Processes.Typed.Proc` |
| `bnd`                     | Fig. 5    | `BorrowedCF.Typed.Predicates.Bounded` |
| `mbl`                     | Fig. 5    | `BorrowedCF.Typed.Predicates.Mobile` |
| `unr`                     | Fig. S-1  | `BorrowedCF.Typed.Predicates.Unr` |
| `new`                     | Fig. S-1  | `BorrowedCF.Typed.Predicates.New` |
| Context equivalence       | Fig. 6    | `BorrowedCF.Context.Equivalence._∶_≈_` |
| Subcontext relation       | Fig. 6    | `BorrowedCF.Context.Subcontext._∶_≼_` |
| Constant typing           | Fig. 7    | `BorrowedCF.Terms.Base.⊢_∶_` |
| Expression typing         | Fig. 8    | `BorrowedCF.Terms.Base._;_⊢_∶_∣_` |
| Process typing            | Fig. 9    | `BorrowedCF.Processes.Typed._;_⊢ₚ_` |
| Expression reduction      | Fig. S-4  | `BorrowedCF.Reduction.Expressions._─→_` |
| Typed process congruence  | Fig. S-5  | `BorrowedCF.Processes.Typed._≋_` |
| Typed process reduction   | Fig. 10   | `BorrowedCF.Reduction.Processes.Typed._─→ₚ_` |
| Untyped process syntax    | Fig. 11   | `BorrowedCF.Processes.UntypedSoup.Config` |
| Untyped process reduction | Fig. 12   | `BorrowedCF.Simulation.FrontCore.FrontStep` |
| Process Translation       | Fig. 13   | `BorrowedCF.Processes.TranslationSoup.U[_]` |
| Closing substitutions     | Def. 7.1  | `BorrowedCF.Algorithmic.Solved.Solving` |
| Algorithmic typing        | Fig. 14   | `BorrowedCF.Algorithmic._;_/_⊢[_]_∶_∣_↑_/_` |
| Blocked processes         | Fig. S-11 | `BorrowedCF.Safety.Blocked.Blocked⁺` |

The paper's unary remote split always allocates at the front of the selected
endpoint's flag list. `FrontStep` restricts the general soup reduction to
`RUS-RSplit` witnesses with an empty `before` list. The general reduction is
retained for the canonical-image and slot-bisimulation proofs; it is not the
paper's executable target relation. `FrontImage` closes `GlobalImage` under
consistent flag permutations, using `BackwardSoup.Statement._≈ˢ_`.
`Simulation.FrontSoup` re-exports the initial-image, step-normalization,
slot-bisimulation and forward-simulation lemmas from `FrontCore` and proves
backward simulation for the same target. Check these modules with:

```sh
agda BorrowedCF/Simulation/FrontSoup.agda
```

### Theorems

| Theorem                          | Agda symbol |
|----------------------------------|-------------|
| 8.1 Expression preservation      | `BorrowedCF.Reduction.Expressions.preservation` |
| 8.2 Process preservation         | `BorrowedCF.Safety.Preservation.preservationₚ` |
| 8.3 Expression progress          | `BorrowedCF.Reduction.Expressions.progress` |
| 8.4 Process progress             | `BorrowedCF.Safety.Progress.progressₚ` |
| 8.5 Forward simulation           | `BorrowedCF.Simulation.FrontCore.forward-front` |
| 8.6 Backward simulation          | `BorrowedCF.Simulation.FrontSoup.backward-front` |
| 8.7 Algorithmic typing soundness | `BorrowedCF.Algorithmic.sound` |
| 8.8 Disjointness of reducible and blocked processes | `BorrowedCF.Completeness.Main.blocked⁺⇒¬step`, `BorrowedCF.Completeness.Main.irreducible⇒blocked⁺` |
| 8.9 Checking completeness        | `BorrowedCF.Completeness.Main.complete⇐` |
| 8.10 Inference completeness       | `BorrowedCF.Completeness.Main.complete⇒` |

### Postulates

Our mechanization postulates three theorems:

```agda
-- (1) BorrowedCF/Kits.agda
∼-ext : ∀ {ϕ₁ ϕ₂ : S₁ →ₖ S₂} → ϕ₁ ∼ ϕ₂ → ϕ₁ ≡ ϕ₂

-- (2) BorrowedCF/Simulation/Support/Base.agda
funext : {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

-- (3) BorrowedCF/Context/Subcontext.agda
_∶_≼?_ : (Γ : Ctx n) → Bin.Decidable (Γ ∶_≼_)
```

Postulates (1) and (2) are functional extensionality. Postulate (3) says that
the subcontext relation is decidable [Saffrich et al. 2024].

No further postulates are reported by

```sh
grep -r '^[[:space:]]*postulate\>' .
```

## Use of generative artificial intelligence

Generative AI assisted with the developments under `Simulation/`, `Safety/`, and
`Completeness/`, and with selected supporting modules: `Terms/DescendAbs.agda`,
`Terms/DescendK.agda`, `Terms/SubstitutionInversion.agda`,
`Types/AtomSnoc.agda`, and `Types/AtomUnsnoc.agda`. The core calculus
definitions and declarative rules precede that work.
