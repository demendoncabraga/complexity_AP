# On the complexity of complementably containing a given subspace

Lean 4 formalization of the paper by Kevin Beanland and Bruno M. Braga.
The project uses real Banach spaces and is pinned to Lean and Mathlib v4.33.1.

## Read the formalization

- [Manuscript](paper/main.tex)
- [Definitions and theorem statements in Lean](docs/LEAN_INDEX.md)
- [Source-to-Lean review](docs/SOURCE_COVERAGE_REVIEW.md)
- [Verification scope](docs/VERIFICATION_SCOPE.md)

The main Borel reduction, both tree theorems, and both complexity upper
bounds are checked. Enflo's existence theorem is deferred. The three
unconditional AP completeness conclusions are reduced to that existence
statement.

## Build and verify

With Git, Python 3, and Lean's version manager `elan` available, run these
commands from this directory.

```sh
lake exe cache get
lake build
python3 scripts/test_audit.py
sh scripts/audit.sh --snapshot
```

The snapshot audit checks the reviewed manuscript fingerprint, the
declaration inventory, source dependencies, and foundational axioms.
See [AGENTS.md](AGENTS.md) for the development workflow.
