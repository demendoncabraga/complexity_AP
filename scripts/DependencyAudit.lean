import PaperFormalization
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  -- Keep these declaration names in sync with coverage.json.
  let roots : Array Name := #[
    ``PaperFormalization.illFounded_isometricOneComplementablyEmbeds,
    ``PaperFormalization.wellFounded_treeSpace_has_property,
    ``PaperFormalization.exists_borelReduction,
    ``PaperFormalization.analytic_family_contains_complemented_copy,
    ``PaperFormalization.analyticSet_complementablyEmbeds,
    ``PaperFormalization.completeAnalytic_complementablyEmbeds,
    ``PaperFormalization.analyticSet_not_hasApproximationProperty,
    ``PaperFormalization.effros_standardBorel_and_compacts,
    ``PaperFormalization.exists_banachCode_linearIsometryEquiv,
    ``PaperFormalization.approximationProperty_isL1StableComplemented,
    ``PaperFormalization.schurProperty_isL1StableComplemented,
    ``PaperFormalization.radonNikodymProperty_isL1Stable,
    ``PaperFormalization.borelAnalytic_isomorphism,
    ``PaperFormalization.borelAnalytic_isometry,
    ``PaperFormalization.borelAnalytic_isComplementedSubspace,
    ``PaperFormalization.borel_parametrized_dualBall,
    ``PaperFormalization.continuous_codedDualPairing_norm,
    ``PaperFormalization.dist_codedDualBallHomeomorph,
    ``PaperFormalization.isHomeomorph_weakStarL1Coordinates,
    ``PaperFormalization.DualCube.range_toLInfinity,
    ``PaperFormalization.NatTree.order_lt_omega_one,
    ``PaperFormalization.NatTree.prune_empty_iff_order_le,
    ``PaperFormalization.NatTree.order_successor_lt,
    ``PaperFormalization.branchOperator,
    ``PaperFormalization.branchProjection_properties,
    ``PaperFormalization.completeAnalytic_complementedClass,
    ``PaperFormalization.completeAnalytic_isometricComplementedClass,
    ``PaperFormalization.NatTree.analyticSet_compl_wellFounded,
    ``PaperFormalization.NatTree.compl_analyticImage_reduces_wellFounded,
    ``PaperFormalization.HasSchurProperty.iff_weaklyConvergent,
    ``PaperFormalization.comap_treeSpace,
    ``PaperFormalization.map_splitRootL1_branchKernelSpan,
    ``PaperFormalization.map_splitRootL1_rootAugmentedKernel,
    ``PaperFormalization.map_splitRootL1_rootCoordinateLine,
    ``PaperFormalization.map_successorL1_branchKernel,
    ``PaperFormalization.completeCoanalytic_approximationPropertyClass,
    ``PaperFormalization.completeAnalytic_union_complementablyEmbeds_noAP,
    ``PaperFormalization.completeAnalytic_union_isometricComplementedClass_noAP
  ]
  let deferredSupport : Array Name := #[]
  let mut todo := roots ++ deferredSupport
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if !((mod == `PaperFormalization) || "PaperFormalization.".isPrefixOf mod.toString) then continue
    let some ci := env.find? name | continue
    let deps := ci.type.getUsedConstants ++ (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])
    todo := todo ++ deps
    rows := rows.push <| Json.mkObj [("name", toJson name.toString), ("module", toJson mod.toString),
      ("deps", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [("roots", toJson (roots.map Name.toString)),
    ("deferredSupport", toJson (deferredSupport.map Name.toString)),
    ("declarations", Json.arr rows)]).compress
