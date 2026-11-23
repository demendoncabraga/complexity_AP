# On the complexity of complementably containing a given subspace

Lean 4 formalization of the paper by Kevin Beanland and Bruno M. Braga.
The project uses real Banach spaces and is pinned to Lean and Mathlib v4.33.1.

## Read the formalization

- [Manuscript](paper/main.tex)
- [Definitions and theorem statements in Lean](docs/LEAN_INDEX.md)
- [Paper result statements](lean/PaperFormalization/PaperStatements.lean)
- [Paper definitions](lean/PaperFormalization/PaperDefinitions.lean)
- [Enflo external theorem](lean/PaperFormalization/PaperAssumptions.lean)
- [Source-to-Lean review](docs/SOURCE_COVERAGE_REVIEW.md)
- [Verification scope](docs/VERIFICATION_SCOPE.md)

The main Borel reduction, both tree theorems, and both complexity upper
bounds are checked. Enflo's existence theorem is the sole named external axiom. The three
AP completeness conclusions are proved in Lean relative to it.

## Build and verify

With Git, Python 3, and Lean's version manager `elan` available, run these
commands from this directory.

```sh
lake exe cache get
lake build
python3 scripts/test_audit.py
sh scripts/audit.sh --terminal
```

The terminal audit checks the reviewed manuscript fingerprint, the complete
declaration inventory, source dependencies, and allowed axioms. It reports
the Enflo dependency explicitly; this is a verification relative to Enflo's
theorem, not a Lean proof of Enflo's theorem.
See [AGENTS.md](AGENTS.md) for the development workflow.

The three Lean review files are imported by `PaperFormalization` and checked by
`lake build`. They display the source definitions and result signatures and record
Enflo’s cited existence theorem as the single named external axiom.
