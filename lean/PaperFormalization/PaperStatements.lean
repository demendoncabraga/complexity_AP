import PaperFormalization.EnfloConsequences
import PaperFormalization.CodingCorollaries
import PaperFormalization.AnalyticUniversality
import PaperFormalization.DualCoding
import PaperFormalization.WellFoundedReduction
import PaperFormalization.TreeReduction

/-! # Statements in the manuscript
Each `#check` resolves the existing proved declaration. The preceding comment
records its full signature without duplicating a theorem or its proof.
The AP completeness corollaries below use the named Enflo assumption. -/

/-
theorem exists_borelReduction (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    ∃ Φ : NatTree → BanachCode, Measurable Φ ∧
      (∀ T, T.IsWellFounded → ∀ p : RealBanachSpace → Prop, IsL1StableProperty p →
        p (RealBanachSpace.of (Φ T).val)) ∧
      (∀ T, T.IsIllFounded → IsometricOneComplementablyEmbeds E (Φ T).val)
-/
#check @PaperFormalization.exists_borelReduction

/-
theorem completeAnalytic_complementedClass (E : BanachCode)
    (p : RealBanachSpace → Prop) (hp : IsL1StableComplementedProperty p)
    (hE : ¬ p (RealBanachSpace.of E.val)) : CompleteAnalytic (complementedClass E)
-/
#check @PaperFormalization.completeAnalytic_complementedClass

/-
theorem completeAnalytic_union_complementablyEmbeds_noAP :
    CompleteAnalytic {X : BanachCode | ∃ E : BanachCode, ¬ HasApproximationProperty E.val ∧
      ComplementablyEmbeds E.val X.val}
-/
#check @PaperFormalization.completeAnalytic_union_complementablyEmbeds_noAP

/-
theorem analytic_family_contains_complemented_copy {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] {g : Y → BanachCode} {B : Set Y}
    (hg : Measurable g) (hB : MeasurableSet B)
    (hA : ∀ X : BanachCode,
      (∀ p : RealBanachSpace → Prop, IsL1StableComplementedProperty p →
        p (RealBanachSpace.of X.val)) → X ∈ g '' B)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ X : BanachCode, X ∈ g '' B ∧ ComplementablyEmbeds E X.val
-/
#check @PaperFormalization.analytic_family_contains_complemented_copy

/-
theorem completeCoanalytic_approximationPropertyClass :
    CompleteCoanalytic approximationPropertyClass
-/
#check @PaperFormalization.completeCoanalytic_approximationPropertyClass

/-
theorem analyticSet_complementablyEmbeds
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SeparableSpace E] :
    @AnalyticSet BanachCode banachCodePolishTopology {X | ComplementablyEmbeds E X.val}
-/
#check @PaperFormalization.analyticSet_complementablyEmbeds

/-
theorem borelCoanalytic_approximationPropertyClass : BorelCoanalytic approximationPropertyClass
-/
#check @PaperFormalization.borelCoanalytic_approximationPropertyClass

/-
theorem borel_parametrized_dualBall :
    Measurable (NonemptyCompacts.toCloseds ∘ codedDualBall) ∧
      MeasurableSet dualPairingSet ∧ Measurable codedDualPairing ∧
      ∀ X : BanachCode,
        (codedDualEvaluation X).toLinearMap.range =
          Submodule.span ℝ (DualCube.toLInfinity '' (codedDualBall X : Set DualCube)) ∧
        codedDualEvaluation X '' Metric.closedBall (0 : StrongDual ℝ X.val) 1 =
          DualCube.toLInfinity '' (codedDualBall X : Set DualCube)
-/
#check @PaperFormalization.borel_parametrized_dualBall

/-
theorem continuous_codedDualPairing_norm (X : BanachCode) :
    @Continuous (↥(codedDualBall X : Set DualCube) × X.val) ℝ
      (@instTopologicalSpaceProd _ _ (TopologicalSpace.induced
        (fun c : ↥(codedDualBall X : Set DualCube) => c.val.toLInfinity) inferInstance)
        inferInstance) inferInstance
      (fun p => ((codedDualBallHomeomorph X).symm p.1).val p.2)
-/
#check @PaperFormalization.continuous_codedDualPairing_norm

/-
theorem dist_codedDualBallHomeomorph (X : BanachCode) (f g : WeakStarUnitBall X.val) :
    dist (codedDualBallHomeomorph X f).val.toLInfinity
      (codedDualBallHomeomorph X g).val.toLInfinity = dist f.val.toStrongDual g.val.toStrongDual
-/
#check @PaperFormalization.dist_codedDualBallHomeomorph

/-
theorem wellFounded_treeSpace_has_property (T : NatTree) (hT : T.IsWellFounded)
    (p : RealBanachSpace → Prop) (hp : IsL1StableProperty p)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : L1 ℕ →L[ℝ] E) : p (RealBanachSpace.of (treeSpace P T))
-/
#check @PaperFormalization.wellFounded_treeSpace_has_property

/-
theorem illFounded_isometricOneComplementablyEmbeds [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (T : NatTree) (hT : T.IsIllFounded)
    (hP : Function.Surjective P)
    (hIso : Isometry (P.toLinearMap.ker.liftQL P le_rfl)) :
    IsometricOneComplementablyEmbeds E (treeSpace P T)
-/
#check @PaperFormalization.illFounded_isometricOneComplementablyEmbeds
