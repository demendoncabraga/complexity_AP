import PaperFormalization.ApproximationAnalytic
import PaperFormalization.ApproximationStability
import PaperFormalization.DescriptiveClasses

namespace PaperFormalization

open Set MeasureTheory TopologicalSpace

theorem borelCoanalytic_approximationPropertyClass : BorelCoanalytic approximationPropertyClass := by
  let t := upgradeStandardBorel BanachCode
  let : TopologicalSpace BanachCode := banachCodePolishTopology
  have : PolishSpace BanachCode := t.toPolishSpace
  have : BorelSpace BanachCode := t.toBorelSpace
  exact (BorelAnalytic.iff_analyticSet _).mpr analyticSet_not_hasApproximationProperty

/-- The union over spaces failing AP coincides with the complement of the AP class. -/
theorem union_complementablyEmbeds_noAP :
    {X : BanachCode | ∃ E : BanachCode, ¬ HasApproximationProperty E.val ∧
      ComplementablyEmbeds E.val X.val} = approximationPropertyClassᶜ := by
  ext X
  change (∃ E : BanachCode, ¬ HasApproximationProperty E.val ∧
    ComplementablyEmbeds E.val X.val) ↔ ¬ HasApproximationProperty X.val
  constructor
  · rintro ⟨E, hE, he⟩ hX
    exact hE (hX.of_complementablyEmbeds he)
  · intro hX
    exact ⟨X, hX, ContinuousLinearMap.id ℝ X.val, ContinuousLinearMap.id ℝ X.val, fun _ => rfl⟩

/-- A single coded space failing AP supplies the hardness reduction. -/
theorem illFounded_reduces_not_approximationProperty {E : BanachCode}
    (hE : ¬ HasApproximationProperty E.val) :
    BorelReduces {T : NatTree | T.IsIllFounded} approximationPropertyClassᶜ := by
  have : SeparableSpace E.val := inferInstance
  obtain ⟨Φ, hΦ, hW, hI⟩ := exists_borelReduction E.val
  refine ⟨Φ, hΦ, Set.ext fun T => ?_⟩
  change (¬ HasApproximationProperty (Φ T).val) ↔ T.IsIllFounded
  constructor
  · intro hn
    by_contra hT
    have hw : T.IsWellFounded := not_nonempty_iff_eq_empty.mp hT
    exact hn (hW T hw (fun F => HasApproximationProperty F) approximationProperty_isL1StableComplemented.1)
  · intro hT hAP
    obtain ⟨i, r, _, hri⟩ := hI T hT
    exact hE (hAP.of_complementablyEmbeds ⟨i.toContinuousLinearMap, r, hri⟩)

/-- Complete coanalyticity of AP is equivalent to the existence of a counterexample to AP. -/
theorem completeCoanalytic_approximationPropertyClass_iff :
    CompleteCoanalytic approximationPropertyClass ↔ (approximationPropertyClassᶜ).Nonempty := by
  constructor
  · intro h
    have hIF : BorelAnalytic {T : NatTree | T.IsIllFounded} :=
      (BorelAnalytic.iff_analyticSet _).mpr NatTree.analyticSet_illFounded
    obtain ⟨f, _, hf⟩ := CompleteAnalytic.reduces
      (show CompleteAnalytic approximationPropertyClassᶜ from h) hIF
    let T : NatTree := ⟨univ, fun _ _ _ _ => mem_univ _⟩
    have hT : T.IsIllFounded := ⟨fun _ => 0, fun _ => mem_univ _⟩
    refine ⟨f T, ?_⟩
    change T ∈ f ⁻¹' approximationPropertyClassᶜ
    rw [hf]
    exact hT
  · rintro ⟨E, hE⟩
    apply completeCoanalytic_iff_wellFounded_reduces.mpr
    refine ⟨borelCoanalytic_approximationPropertyClass, ?_⟩
    simpa only [NatTree.wellFounded_eq_compl_illFounded, compl_compl] using
      (illFounded_reduces_not_approximationProperty hE).compl

/-- The complete-analytic union corollary requires exactly the same existence result. -/
theorem completeAnalytic_union_complementablyEmbeds_noAP_iff :
    CompleteAnalytic {X : BanachCode | ∃ E : BanachCode, ¬ HasApproximationProperty E.val ∧
      ComplementablyEmbeds E.val X.val} ↔ (approximationPropertyClassᶜ).Nonempty := by
  rw [union_complementablyEmbeds_noAP, ← CompleteCoanalytic]
  exact completeCoanalytic_approximationPropertyClass_iff

end PaperFormalization
