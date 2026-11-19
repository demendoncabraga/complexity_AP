# Source coverage review

The source is `paper/main.tex`, *On the complexity of complementably containing
a given subspace*. The inventory covers the labeled theorem chain, its definitions, and the
cited results used by the Lean proofs. The introductory open problem,
historical results, and examples cited for context are outside its scope.
The [Lean index](LEAN_INDEX.md) links the manuscript statements to their
formal counterparts.

`PaperFormalization.Basic` defines the real approximation property with finite
dimensional operator range and uniform error on each compact set. An
isomorphic complemented copy is expressed by a continuous linear map with a
continuous linear left inverse. Its isometric counterpart uses a linear
isometry and a contractive left inverse, including the zero space. Trees use
lists of naturals and prefix closure. The branch condition includes length zero.
The topology is induced by the Boolean characteristic-function coding,
each node-membership cylinder is clopen, and the tree space is Polish.
The closed branch-incidence relation gives analyticity of the ill-founded
trees.

## Proposition 2.2

The revised proof of `ThmAPisCoanalytic` quantifies over compact subsets of
the ambient space C[0,1] containing zero. Thus K ∩ X is a nonempty compact
set of vectors. Its Borel selectors and the approximation-property
equivalence are verified. The cited parametrized dual-ball coding
is reviewed below.

## Tree reduction

The real ℓ₁ construction uses Mathlib's summation operator and bounded
coordinatewise maps. The common branch-kernel span is represented as the
closure of the supremum of its included kernels. The tree space is defined
as the closed span of the images of its coordinate vectors in the ambient
quotient. The full preimage of this subspace is proved to be the closure of
ℓ₁(T) + Z. A quotient subspace is identified isometrically with the quotient
of its full preimage by the restricted kernel.

The ill-founded theorem uses the paper's surjectivity and isometry hypotheses
on the induced operator quotient map. The proof collapses all tree coordinates
by depth and uses the branch inclusion to obtain the isometric section. Both
descend contractively to the quotients.

## Borel assignment and well-founded induction

The assignment is checked for an ambient linear isometric embedding of the
quotient into C[0,1]. The open-hit proof indexes a countable union by finite
sets of nodes. For each fixed finite set, whether the associated real span
meets the open set is independent of the tree. Membership of all those
nodes is a finite intersection of clopen cylinders. The coded output is
proved to be the isometric image of the corresponding tree space. The
standardness of the Effros coding is verified independently.

The well-founded argument can use accessibility of the immediate successor
subtree relation. An infinite descending chain of successor subtrees would
supply an infinite branch. This gives Lean's induction principle.

## Existence of the operator quotient

The construction uses a dense sequence in the target's closed unit ball.
The associated synthesis operator from ℓ₁ is a contraction. Correcting the
residual by a convergent geometric series gives exact preimages with norms
arbitrarily close to the norm of the target vector. This proves surjectivity
and isometry of the induced quotient operator for all separable real Banach
spaces, including the zero space.

## Well-founded successor decomposition

The coordinate operators give the branch-kernel identity in
`Eq.DimKernels` and map the closed common kernel onto the coordinatewise
tail kernels. Deleting the root and assembling the successor blocks
descend to inverse contractions. The quotient of a countable ℓ₁ sum by
the coordinatewise kernel is identified isometrically with the sum of the
quotients using almost-minimal coordinate lifts with summable errors.

The ambient identification is proved to send each node generator to its
specified successor coordinate. Finite partial sums verify that its
restriction is onto the successor subspace. The resulting isometric
decomposition in `Claim.left.behind` indexes all natural numbers, with
zero spaces at missing children. The root-only dimension bound is
verified separately.

## Well-founded theorem and reduction assembly

The checked well-founded theorem uses successor-tree induction. The
induction predicate quantifies over the target Banach space and the
operator, so the induction hypothesis applies to the tail operator
after passing to the quotient of the target by its root image. The
root line is at most one dimensional and is split off by Mathlib's
finite-dimensional complement theorem. A two-coordinate ℓ₁ sum proves
the required product stability from the stated sum hypothesis.

The two tree cases are combined with the Borel assignment in
`exists_borelReduction_of_ambientEmbedding`. This is the assembly step
of the main theorem. Banach–Mazur provides the required ambient embedding.

## Banach–Mazur and the main theorem

The weak-star dual unit ball is compact by Banach–Alaoglu and metrizable for
a separable source. Evaluation gives a linear isometry by Hahn–Banach.
Precomposition with a continuous surjection from Cantor space preserves
the supremum norm. Affine interpolation between neighboring Cantor points
extends those functions to the unit interval linearly and isometrically.
Continuity at Cantor points follows from the affine average of the two
endpoint distances. This supplies the ambient isometry in the paper's
Borel assignment for the separable tree quotient. The main theorem now
constructs a single measurable map satisfying both conclusions.

## Completeness of the tree classes and analytic universality

An analytic set in a Polish presentation is reduced to ill-foundedness by
the tree of finite prefixes whose extensions give arbitrarily close
approximations to the target. Node membership is an open condition, and a
branch produces a sequence of approximants converging coordinatewise.
Passing to complements gives the corresponding Borel reduction to
well-foundedness. A universal family of analytic sets is obtained from
the trees of paired prefixes of closed relations on Baire space. Its
diagonal complement and the completeness reduction show that the
well-founded trees are non-analytic.

The universality corollary uses the manuscript's presentation of an
analytic family as a Borel image of a Borel subset of a standard Borel
space. Equality in the Effros coding is measurable because hit tests
on a countable open basis distinguish its closed subspaces. The preimage
of that family under the reduction is therefore analytic and strictly
contains the well-founded trees. An ill-founded witness
supplies the complemented copy.

## Borel selectors and coding of compact intersections

The selector proof takes limits of measurable choices from a fixed dense
sequence. The measurable distances to closed fibers also give the Borel
point-membership test, and testing the dense selectors against a second
subspace gives Borel inclusion. The sequence of selectors encodes a closed
subspace into a Borel subset of the countable power of its ambient space.
Closed span is the measurable inverse, with open hits detected by finite
rational combinations.

The compact parameter in Proposition 2.2 uses the Vietoris space of
nonempty compact sets and its closed subset of sets containing zero.
For an open hit of a compact intersection, the proof tests arbitrarily
small distances to the subspace within a countable family of balls with
closure contained in the open set. Compactness provides a point where
the distance vanishes. The selector theorem then gives Borel dense
sequences in these intersections.

## Analyticity of complemented containment

The proof of Proposition 2.1 uses a countable code for the values of a
bounded linear embedding and a bounded linear left inverse. The left
inverse is prescribed on the interleaving of the ambient subspace's
dense selectors and the image of the fixed space's dense sequence.
Norm inequalities on rational combinations extend to real combinations
by continuity. The resulting operators agree with the prescribed values,
so their composition is the identity by density. The code tests are
Borel, and projecting the witness set gives the analytic upper bound.

The complete-analytic corollary combines this upper bound with the main
tree reduction. A complemented embedding into the value at a well-founded
tree would transfer the chosen property to the fixed space, contradicting
the hypothesis. An ill-founded tree gives the required copy directly.

## Coanalyticity of the approximation property

The proof uses a fixed weak-star dense sequence in the unit dual ball
of the ambient C[0,1]. Hahn–Banach extends each unit functional on a
closed subspace with the same norm. Joint evaluation on the ambient
dual ball is continuous, which yields uniform approximation on each
compact set by the fixed countable family. Finite-rank operators
decompose into finitely many unit functionals times vectors. Replacing
both the functionals and vectors by their countable approximants gives
the ambient compact test. Testing on the Borel dense selectors for the
compact intersections yields a Borel relation. The projection of its
complement is the class of spaces failing the approximation property.

A separate lemma transfers the approximation property across a bounded
linear retraction by composing finite-rank approximants on the larger space.

## Joint operator relations and the isometric variants

The joint codes prescribe the two operators on dense sequences in the
two varying spaces. When the inclusion is fixed, only the retraction
is coded. Two unit norm bounds enforce preservation of the norm.
Surjectivity is checked by approximating a dense sequence in the target
by images of points from the source sequence. The resulting Borel
witness sets yield the isomorphism, linear isometry, and complemented
containment relations. The fixed-space isometric completeness result
uses the same tree reduction as the isomorphic result, with the stronger
contractive copy supplied on ill-founded trees.

## Effros hyperspaces and the parametrized dual

The general closed-set Effros space uses a dense sequence for a nonempty
fiber and a Boolean coordinate for the empty fiber. The inverse takes
the closure of the range. Closed sets are compact exactly when they pass
countable finite-cover tests. These results verify that the compact
subspace is Borel and standard Borel.

For a coded real Banach space, evaluation on Borel dense selectors of
its unit ball embeds the dual isometrically in ℓ∞. Its range is the
linear span of the coded compact ball, and the product coordinate cube
is homeomorphic to the weak-star dual unit ball of ℓ₁. Hahn–Banach makes
restriction from the fixed ambient dual ball onto each space's dual ball
surjective. Restricting a single countable dense family proves Borel
measurability of the compact-ball assignment. Evaluation on a vector is
a limit of scaled coordinate evaluations at measurable choices of nearby
selectors. On each fiber the pairing is jointly norm-continuous and the
weak-star identification is a homeomorphism.

## Branch coordinates and the order of a tree

The branch enumeration is a surjective linear isometry on the supported
ℓ₁ space. Folding coordinates to the same depth on a chosen branch gives
a norm-one projection that sends the common closed kernel span into the
included kernel on that branch. The transfinite pruning is also defined
directly, with intersection at limit ordinals. The accessible successor
rank characterizes which stages retain the root, proving countability of
the order and strict decrease at each actual successor. The checked
well-founded theorem uses the equivalent induction by accessibility.

## Stability of the three Banach-space properties

For AP, finite-coordinate truncations approximate the identity uniformly
on compact sets. The component approximations combine to a finite-rank
operator on an arbitrary ℓ₁ sum. For the Schur property, a weakly null
sequence failing norm convergence would provide disjoint finite blocks
with large mass. Component norming functionals on the blocks assemble
into one bounded functional that contradicts weak convergence. For the
Radon–Nikodým property, the component measures have Bochner densities.
Total variation bounds the sum of their L¹ norms through each finite
coordinate truncation, so their unconditional L¹ sum is a density of the
original vector measure. The real case uses the signed-measure
Radon–Nikodým theorem.

## Completeness conclusions depending on Enflo

The two unions over spaces failing AP, whether copies are isomorphic or
isometric, both equal the complement of AP by the inheritance lemma and
the identity embedding. The tree reduction gives Borel hardness as soon
as there is one separable Banach space failing AP. Lean proves that each
of the three unconditional AP completeness conclusions is equivalent to
that single existence statement. Enflo's theorem is deferred by the
author, so these conclusions remain open in the unconditional inventory.
