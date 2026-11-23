import PaperFormalization.CodingCorollaries
import PaperFormalization.PaperAssumptions

namespace PaperFormalization

open Set

/-- Corollary Cor.Smith, relative to Enflo's existence theorem. -/
theorem completeCoanalytic_approximationPropertyClass :
    CompleteCoanalytic approximationPropertyClass := by
  exact completeCoanalytic_approximationPropertyClass_iff.mpr
    (exists_coded_noAP_iff.mpr enfloNoAP)

/-- Corollary Corollary.CCE.anyE.CA, relative to Enflo's existence theorem. -/
theorem completeAnalytic_union_complementablyEmbeds_noAP :
    CompleteAnalytic {X : BanachCode | ∃ E : BanachCode,
      ¬ HasApproximationProperty E.val ∧ ComplementablyEmbeds E.val X.val} := by
  exact completeAnalytic_union_complementablyEmbeds_noAP_iff.mpr
    (exists_coded_noAP_iff.mpr enfloNoAP)

/-- The isometric version of the union corollary, relative to Enflo. -/
theorem completeAnalytic_union_isometricComplementedClass_noAP :
    CompleteAnalytic {X : BanachCode | ∃ E : BanachCode,
      ¬ HasApproximationProperty E.val ∧ X ∈ isometricComplementedClass E} := by
  exact completeAnalytic_union_isometricComplementedClass_noAP_iff.mpr
    (exists_coded_noAP_iff.mpr enfloNoAP)

end PaperFormalization
