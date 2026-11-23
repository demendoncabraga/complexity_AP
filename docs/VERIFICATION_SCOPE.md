# Verification scope

The target is the real-scalar manuscript, its definitions, supporting
results, and corollaries. The introductory open problem, historical
results, and examples cited for context are outside the proof inventory.

Lean verifies the main Borel reduction, the two tree theorems, the
tree-space construction and ordinal pruning, and the Banach–Mazur
coding. The tree classes have the claimed Borel completeness and give
the analytic-family universality corollary.

Both upper-bound propositions are verified. The formalization includes
the joint analytic relations, the fixed-space isomorphic and isometric
completeness conclusions, Borel selectors for compact intersections, the
standard Borel Effros hyperspaces, and the recalled parametrized
weak-star dual-ball theorem. AP, the Schur property, and the
Radon–Nikodým property are proved stable under arbitrary ℓ₁ sums.

Enflo's existence theorem is the sole external mathematical axiom, stated in
`PaperFormalization.PaperAssumptions`. The three AP completeness conclusions
are Lean theorems that depend explicitly on it. The terminal audit permits
this named axiom only in those conclusions, checks that they depend on it,
and reports verification relative to Enflo (1973, Theorem 1). The theorem
itself is not formalized in Lean.
