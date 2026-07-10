# Agda Supplement for `Context-Free Session Types with Borrowing`

This is the Agda formalization accompanying the paper. It defines the calculus
(CSTB), its type system, the untyped run-time calculus and its translation, and
proves the metatheoretical results marked with the Agda bird in the paper.

Note: Checking all files may take a serious amount of time (up to half an hour).

## Requirements

Agda: [v2.8.0](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html)
Agda `stdlib`: [v2.3](https://agda.readthedocs.io/en/v2.8.0/tools/package-system.html#example-using-the-standard-library)

Register `borrowed-cf.agda-lib` (and `standard-library`) with Agda, then
type-check any module, e.g. `agda BorrowedCF/Simulation2/Forward.agda`.

## Structure

```
│
├── BorrowedCF
│   ├── Prelude.agda        -- shared standard-library re-exports and notation
│   ├── Kits.agda           -- generic de Bruijn renaming/substitution framework ("kits")
│   ├── Types               -- session type language: syntax, substitution,
│   │                          equivalence, predicates, and unification
│   ├── Terms.agda          -- expression (term) syntax
│   ├── Context             -- typing contexts and their algebra (join/split,
│   │                          subcontext, domain, equivalence, substitution)
│   ├── Processes           -- process syntax and the translation
│   │   ├── Typed.agda        -- typed source processes
│   │   ├── Untyped.agda      -- untyped run-time configurations (target calculus)
│   │   ├── Translation.agda  -- process translation U[_] and structural congruence ≋
│   ├── Reduction           -- operational semantics and type-safety proofs
│   │   ├── Expressions.agda  -- expression reduction (and expression safety)
│   │   └── Processes         -- Typed.agda / Untyped.agda: source and target reduction
│   ├── Algorithmic.agda    -- bidirectional algorithmic typing
│   ├── Algorithmic         -- Solved.agda: constraint solving for algorithmic typing
│   └── Simulation          -- operational-correspondence development: translation
└── README.md              -- this file
```

## Theorems from the paper

- **Type safety** (expression/process preservation and progress) —
  `BorrowedCF/Reduction/Expressions.agda`.
- **Weak simulation for the translation** — `BorrowedCF/Simulation/Forward.agda`
  (`sim→`) and `BorrowedCF/Simulation2/Backward.agda` (`sim←`); the translation
  `U[_]` is in
  `BorrowedCF/Processes/Translation.agda`.
- **Soundness of algorithmic typing** —
  `BorrowedCF/Algorithmic.agda` and `BorrowedCF/Algorithmic/Solved.agda`.

## Note on usage of generative artificial intelligence

We used genAI for the simulation proof and for some helper lemmas. Only the `Simulation/` folder and `TypedEq.agda`, `DescendAbs.agda` and `DescendK.agda`, `AtomSnoc.agda` and `AtomUnsnoc.agda` contains 
genAI code. The definitions and all other proofs are written by hand. 