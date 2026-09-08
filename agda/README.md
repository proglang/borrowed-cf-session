# Agda Supplement for *Context-Free Session Types with Borrowing*

This directory contains the Agda formalization accompanying the paper. It
defines the CSTB calculus, its declarative and algorithmic type systems, typed
source processes, two presentations of the untyped run-time calculus, and the
main metatheoretic results.

The current development includes process preservation and progress,
soundness and completeness of algorithmic typing, and forward and backward
simulation for the strict soup run time. See [CHANGES.md](CHANGES.md) for the
detailed theorem statements and the changes made while completing these
proofs.

## Requirements

- [Agda 2.8.0](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html)
- [Agda standard library 2.4](https://agda.readthedocs.io/en/v2.8.0/tools/package-system.html#example-using-the-standard-library)

Register `borrowed-cf.agda-lib` and `standard-library` with Agda. Run checks
from this `agda/` directory, for example:

```console
agda BorrowedCF/Algorithmic.agda
agda BorrowedCF/Completeness.agda
agda BorrowedCF/Safety/Preservation.agda
agda BorrowedCF/Safety/Progress.agda
agda BorrowedCF/Simulation/ForwardSoup/Local.agda
agda BorrowedCF/Simulation/BackwardSoup/Simulation.agda
```

The larger safety and simulation entry points have substantial dependency
graphs, so a clean build can take significant time and memory.

## Main results

| Result | Entry point |
|---|---|
| Algorithmic soundness (`sound`) | [`BorrowedCF/Algorithmic.agda`](BorrowedCF/Algorithmic.agda) |
| Algorithmic completeness, inference and checking (`complete⇒`, `complete⇐`) | [`BorrowedCF/Completeness.agda`](BorrowedCF/Completeness.agda) |
| Process preservation (`preservationₚ`) | [`BorrowedCF/Safety/Preservation.agda`](BorrowedCF/Safety/Preservation.agda) |
| Process progress (`progressₚ`) and strengthened progress (`progress⁺ₚ`) | [`BorrowedCF/Safety/Progress.agda`](BorrowedCF/Safety/Progress.agda) |
| Forward simulation into the strict soup run time (`sim-global`) | [`BorrowedCF/Simulation/ForwardSoup/Local.agda`](BorrowedCF/Simulation/ForwardSoup/Local.agda) |
| Backward simulation from the strict soup run time (`backward-sim`) | [`BorrowedCF/Simulation/BackwardSoup/Simulation.agda`](BorrowedCF/Simulation/BackwardSoup/Simulation.agda) |

The completeness theorems reconstruct bidirectional algorithmic derivations
from declarative derivations for solved contexts, terms, and result types. They
assume `LinStruct Γ γ`: a linear variable occurs at most once in the
structural context. This condition is necessary; a mechanized counterexample
is in
[`BorrowedCF/Completeness/Probe/LinNeeded.agda`](BorrowedCF/Completeness/Probe/LinNeeded.agda).
The full statement is documented in
[`BorrowedCF/Completeness/Base.agda`](BorrowedCF/Completeness/Base.agda).

The strict-soup backward theorem is stated up to a local renumbering of an
endpoint's φ slots, the equivalence required by right split. Its statement is in
[`BorrowedCF/Simulation/BackwardSoup/Statement.agda`](BorrowedCF/Simulation/BackwardSoup/Statement.agda).

`BorrowedCF/Simulation/Forward.agda` is the retained forward proof for the
older tree-shaped run time. Its incomplete backward counterpart has been
removed. The maintained, bidirectional operational-correspondence development
is the `ForwardSoup/` and `BackwardSoup/` pair above.

## Structure

```text
BorrowedCF/
├── Prelude.agda, FinKits.agda, Kits.agda
│   Shared notation and generic de Bruijn renaming/substitution machinery.
├── Types/ and Types.agda
│   Session-type syntax, substitution, equivalence, predicates, and unification.
├── Terms/ and Terms.agda
│   Expression syntax, declarative typing, and substitution support.
├── Context/ and Context.agda
│   Structural contexts, joins, equivalence, subcontexts, and constraints.
├── Processes/
│   Typed processes, tree and soup run times, and both translations.
├── Reduction/
│   Expression and process reductions for the typed and untyped calculi.
├── Algorithmic.agda and Algorithmic/Solved.agda
│   Bidirectional typing, generated constraints, closing substitutions, and soundness.
├── Completeness/
│   Algorithmic completeness, including splitting, weakening, scope, and restriction.
├── Safety/
│   Process preservation, blocked configurations, and progress.
└── Simulation/
    Forward and backward operational correspondence; the strict soup proofs
    are under ForwardSoup/ and BackwardSoup/.
```

## Use of generative artificial intelligence

Generative AI assisted with the developments under `Simulation/`, `Safety/`,
and `Completeness/`, and with selected supporting modules: `TypedEq.agda`,
`Terms/DescendAbs.agda`, `Terms/DescendK.agda`, `Types/AtomSnoc.agda`, and
`Types/AtomUnsnoc.agda`. The core calculus definitions and declarative rules
precede that work.
