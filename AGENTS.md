# Paper formalization

Use the author's article in `paper/main.tex` as the authoritative source.
Preserve the manuscript unless the author requests edits. Keep Lean and Mathlib
pins unchanged unless the author requests an upgrade.

Inventory the manuscript definitions, stated results, and proof dependencies.
Record a unique ID, source reference, description, and status (`not_started`,
`in_progress`, or `verified`) for each entry in `lean/coverage.json`.
Record the fully qualified Lean declaration for every verified entry.
Set `source_sha256` to the reviewed source's SHA-256 digest. Keep
`paper_roots` synchronized with the final manuscript declarations in
`scripts/DependencyAudit.lean`.

Write modules under `lean/PaperFormalization/` and import them from
`lean/PaperFormalization.lean`. Preserve quantifiers, scalar fields, hypotheses,
and generality. Prove cited dependencies locally or use checked library results.
Report ambiguities or unavailable cited results to the author. Do not add project
axioms, external assumptions, or proof placeholders. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted foundational axioms.

Run `python3 scripts/test_audit.py` and `sh scripts/audit.sh` during development.
After the inventory and proofs are complete, run `sh scripts/audit.sh --terminal`
and review the Lean statements against the manuscript. Keep the review and scope
in `docs/SOURCE_COVERAGE_REVIEW.md` and `docs/VERIFICATION_SCOPE.md`.
Preserve licenses and provenance for any vendored dependencies.
