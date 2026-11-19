import PaperFormalization.ApproximationCorollaries
import PaperFormalization.JointComplementedAnalytic

namespace PaperFormalization

open Set Topology TopologicalSpace

/-- Every separable real Banach space has a linearly isometric closed-subspace code. -/
theorem exists_banachCode_linearIsometryEquiv (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [SeparableSpace E] :
    ∃ X : BanachCode, Nonempty (E ≃ₗᵢ[ℝ] X.val) := by
  obtain ⟨i⟩ := exists_banachAmbient_linearIsometry E
  let X : BanachCode := ⟨i.toLinearMap.range, i.isometry.isClosedEmbedding.isClosed_range⟩
  let j : E →ₗᵢ[ℝ] X.val :=
    ⟨i.toLinearMap.codRestrict X.val (fun x => ⟨x, rfl⟩), i.norm_map⟩
  exact ⟨X, ⟨LinearIsometryEquiv.ofSurjective j fun ⟨_, x, rfl⟩ => ⟨x, rfl⟩⟩⟩

/-- Existence of a Banach-space counterexample to AP is equivalent to a coded one. -/
theorem exists_coded_noAP_iff :
    (approximationPropertyClassᶜ).Nonempty ↔
      ∃ E : RealBanachSpace, SeparableSpace E ∧ ¬ HasApproximationProperty E := by
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨RealBanachSpace.of X.val, inferInstanceAs (SeparableSpace X.val), hX⟩
  · rintro ⟨E, hsep, hE⟩
    obtain ⟨X, ⟨i⟩⟩ := exists_banachCode_linearIsometryEquiv E
    exact ⟨X, fun hX => hE (HasApproximationProperty.of_equiv hX i.symm.toContinuousLinearEquiv)⟩

theorem completeAnalytic_complementedClass (E : BanachCode)
    (p : RealBanachSpace → Prop) (hp : IsL1StableComplementedProperty p)
    (hE : ¬ p (RealBanachSpace.of E.val)) : CompleteAnalytic (complementedClass E) := by
  rw [completeAnalytic_iff_illFounded_reduces]
  have : StandardBorelSpace BanachCode := banachCode_standardBorel
  exact ⟨borelAnalytic_complementablyEmbeds_relation.preimage (measurable_const.prodMk measurable_id),
    exists_reduction_complementablyEmbeds E.val p hp hE⟩

theorem union_isometricComplementedClass_noAP :
    {X : BanachCode | ∃ E : BanachCode,
      ¬ HasApproximationProperty E.val ∧ X ∈ isometricComplementedClass E} =
      approximationPropertyClassᶜ := by
  ext X
  change (∃ E : BanachCode, ¬ HasApproximationProperty E.val ∧
    IsometricallyComplementablyEmbeds E.val X.val) ↔ ¬ HasApproximationProperty X.val
  constructor
  · rintro ⟨E, hE, he⟩ hAP
    exact hE (hAP.of_complementablyEmbeds he.complementablyEmbeds)
  · intro hX
    exact ⟨X, hX, LinearIsometry.id, ContinuousLinearMap.id ℝ X.val, fun _ => rfl⟩

/-- The isometric union variant also requires just one separable counterexample to AP. -/
theorem completeAnalytic_union_isometricComplementedClass_noAP_iff :
    CompleteAnalytic {X : BanachCode | ∃ E : BanachCode,
      ¬ HasApproximationProperty E.val ∧ X ∈ isometricComplementedClass E} ↔
        (approximationPropertyClassᶜ).Nonempty := by
  rw [union_isometricComplementedClass_noAP, ← CompleteCoanalytic]
  exact completeCoanalytic_approximationPropertyClass_iff

end PaperFormalization
