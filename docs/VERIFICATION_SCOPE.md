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

Enflo's existence theorem is deferred at the author's request. Lean
proves that its existence conclusion is exactly what remains to deduce
complete coanalyticity of AP and complete analyticity of both unions
over spaces failing AP. The unconditional versions of those three
claims remain open. The snapshot audit checks the implemented proofs,
including the four registered declarations supporting the deferred
conclusions. The terminal audit requires the unconditional claims.
