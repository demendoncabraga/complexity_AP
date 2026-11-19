# Lean definitions and theorem statements

All declarations below are in the `PaperFormalization` namespace. To use
them from Lean, write `import PaperFormalization`. The links open the
declarations in source, with their full hypotheses and conclusions.

## Definitions

| Manuscript terminology | Lean definition |
| --- | --- |
| Trees, branches, well-foundedness | [`NatTree`](../lean/PaperFormalization/Basic.lean#L23), [`branches`](../lean/PaperFormalization/Basic.lean#L28), [`IsWellFounded`](../lean/PaperFormalization/Basic.lean#L32), [`IsIllFounded`](../lean/PaperFormalization/Basic.lean#L35) |
| Ordinal pruning and tree order | [`prune`](../lean/PaperFormalization/TreeOrder.lean#L27), [`order`](../lean/PaperFormalization/TreeOrder.lean#L128) |
| Banach codes and Effros structure | [`ClosedSubspaces`](../lean/PaperFormalization/BorelAssignment.lean#L7), [`BanachAmbient`](../lean/PaperFormalization/BorelAssignment.lean#L56), [`BanachCode`](../lean/PaperFormalization/BorelAssignment.lean#L59), [`hit`](../lean/PaperFormalization/EffrosHyperspace.lean#L18) |
| Analytic and coanalytic sets, reductions, completeness | [`BorelAnalytic`](../lean/PaperFormalization/DescriptiveClasses.lean#L10), [`BorelCoanalytic`](../lean/PaperFormalization/DescriptiveClasses.lean#L14), [`BorelReduces`](../lean/PaperFormalization/DescriptiveClasses.lean#L18), [`CompleteAnalytic`](../lean/PaperFormalization/DescriptiveClasses.lean#L39), [`CompleteCoanalytic`](../lean/PaperFormalization/DescriptiveClasses.lean#L44) |
| Complemented, isometric, and contractively complemented embeddings | [`ComplementablyEmbeds`](../lean/PaperFormalization/Basic.lean#L13), [`IsometricallyComplementablyEmbeds`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L10), [`IsometricOneComplementablyEmbeds`](../lean/PaperFormalization/Basic.lean#L18) |
| Classes `CC_E` and its isometric counterpart | [`complementedClass`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L339), [`isometricComplementedClass`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L335) |
| Properties in the classes ℂ and ℂ꜀ | [`IsL1StableProperty`](../lean/PaperFormalization/BanachProperties.lean#L26), [`IsL1StableComplementedProperty`](../lean/PaperFormalization/BanachProperties.lean#L34) |
| AP, Schur, and Radon–Nikodým | [`HasApproximationProperty`](../lean/PaperFormalization/Basic.lean#L6), [`approximationPropertyClass`](../lean/PaperFormalization/ApproximationAnalytic.lean#L177), [`HasSchurProperty`](../lean/PaperFormalization/SchurProperty.lean#L13), [`HasRadonNikodymProperty`](../lean/PaperFormalization/RadonNikodymProperty.lean#L13) |
| ℓ₁ on a tree, the branch operator, and the common kernel | [`L1`](../lean/PaperFormalization/TreeReduction.lean#L6), [`supportedL1`](../lean/PaperFormalization/TreeReduction.lean#L79), [`branchOperator`](../lean/PaperFormalization/BranchGeometry.lean#L78), [`branchKernelSpan`](../lean/PaperFormalization/TreeReduction.lean#L60) |
| Tree space and its assignment to a Banach code | [`treeSpace`](../lean/PaperFormalization/TreeReduction.lean#L73), [`treeAssignment`](../lean/PaperFormalization/BorelAssignment.lean#L67) |

Lean numbers the children of a tree by `ℕ` starting at zero. Shifting the
child labels by one gives the paper's positive-integer convention. The
empty list is the root, and ℓ₁ coordinates are indexed by depth from zero.

## Theorem statements in manuscript order

| Result | Lean statement |
| --- | --- |
| [Theorem 1.1](../paper/main.tex#L147) · Main Borel reduction | [`exists_borelReduction`](../lean/PaperFormalization/MainReduction.lean#L17) |
| [Corollary 1.2](../paper/main.tex#L164) · Complete analyticity of fixed-space complemented containment | [`completeAnalytic_complementedClass`](../lean/PaperFormalization/CodingCorollaries.lean#L29), [`completeAnalytic_complementablyEmbeds`](../lean/PaperFormalization/ComplementedAnalytic.lean#L185) |
| [Corollary 1.5](../paper/main.tex#L192) · Union over spaces failing AP | [`completeAnalytic_union_complementablyEmbeds_noAP_iff`](../lean/PaperFormalization/ApproximationCorollaries.lean#L68) |
| [Isometric variants](../paper/main.tex#L199) · Fixed space and union | [`completeAnalytic_isometricComplementedClass`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L348), [`completeAnalytic_union_isometricComplementedClass_noAP_iff`](../lean/PaperFormalization/CodingCorollaries.lean#L51) |
| [Corollary 1.6](../paper/main.tex#L209) · Universality of analytic families | [`analytic_family_contains_complemented_copy`](../lean/PaperFormalization/AnalyticUniversality.lean#L22) |
| [Corollary 1.7](../paper/main.tex#L222) · Complete coanalyticity of AP | [`completeCoanalytic_approximationPropertyClass_iff`](../lean/PaperFormalization/ApproximationCorollaries.lean#L47) |
| [Proposition 2.1](../paper/main.tex#L245) · Analyticity of fixed-space complemented containment | [`analyticSet_complementablyEmbeds`](../lean/PaperFormalization/ComplementedAnalytic.lean#L101), [`borelAnalytic_isComplementedSubspace`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L421) |
| [Proposition 2.2](../paper/main.tex#L276) · Coanalyticity of AP | [`borelCoanalytic_approximationPropertyClass`](../lean/PaperFormalization/ApproximationCorollaries.lean#L9), [`analyticSet_not_hasApproximationProperty`](../lean/PaperFormalization/ApproximationAnalytic.lean#L180) |
| [Theorem 2.3](../paper/main.tex#L292) · Parametrized dual-ball coding | [`borel_parametrized_dualBall`](../lean/PaperFormalization/DualCoding.lean#L384), [`continuous_codedDualPairing_norm`](../lean/PaperFormalization/DualCoding.lean#L344), [`dist_codedDualBallHomeomorph`](../lean/PaperFormalization/DualCoding.lean#L198), [`codedDualBallHomeomorph`](../lean/PaperFormalization/DualCoding.lean#L181) |
| [Theorem 3.1](../paper/main.tex#L352) · Well-founded tree spaces | [`wellFounded_treeSpace_has_property`](../lean/PaperFormalization/WellFoundedReduction.lean#L11) |
| [Theorem 3.2](../paper/main.tex#L447) · Ill-founded tree spaces | [`illFounded_isometricOneComplementablyEmbeds`](../lean/PaperFormalization/TreeReduction.lean#L255) |

The equivalences for Corollaries 1.5 and 1.7 and the isometric union isolate
the same deferred hypothesis, the existence of a separable real Banach
space without AP. See the [verification scope](VERIFICATION_SCOPE.md).

## Supporting results

| Topic | Lean statement |
| --- | --- |
| Effros hyperspace and the Banach–Mazur coding | [`effros_standardBorel_and_compacts`](../lean/PaperFormalization/EffrosHyperspace.lean#L183), [`exists_banachCode_linearIsometryEquiv`](../lean/PaperFormalization/CodingCorollaries.lean#L9) |
| Joint relations | [`borelAnalytic_isomorphism`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L309), [`borelAnalytic_isometry`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L322), [`borelAnalytic_complementablyEmbeds_relation`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L292), [`borelAnalytic_isometricallyComplementablyEmbeds_relation`](../lean/PaperFormalization/JointComplementedAnalytic.lean#L297) |
| Tree completeness and well-foundedness | [`analyticImage_reduces_illFounded`](../lean/PaperFormalization/TreeCompleteness.lean#L88), [`compl_analyticImage_reduces_wellFounded`](../lean/PaperFormalization/TreeCompleteness.lean#L104), [`not_analyticSet_wellFounded`](../lean/PaperFormalization/TreeCompleteness.lean#L211) |
| Successor decomposition and Borel assignment | [`treeSpaceRootQuotientL1Equiv`](../lean/PaperFormalization/AmbientSuccessor.lean#L183), [`measurable_treeAssignment`](../lean/PaperFormalization/BorelAssignment.lean#L71), [`treeAssignment_isometry`](../lean/PaperFormalization/BorelAssignment.lean#L90) |
| Closure under ℓ₁ sums | [`approximationProperty_isL1StableComplemented`](../lean/PaperFormalization/ApproximationStability.lean#L119), [`schurProperty_isL1StableComplemented`](../lean/PaperFormalization/SchurProperty.lean#L179), [`radonNikodymProperty_isL1Stable`](../lean/PaperFormalization/RadonNikodymProperty.lean#L192) |
