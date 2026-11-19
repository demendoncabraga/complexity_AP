import PaperFormalization.MainReduction
import PaperFormalization.TreeCompleteness
import PaperFormalization.EffrosEquality

namespace PaperFormalization

open MeasureTheory Set

theorem analyticSet_preimage_banachCode_image {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] {f : NatTree → BanachCode} {g : Y → BanachCode} {B : Set Y}
    (hf : Measurable f) (hg : Measurable g) (hB : MeasurableSet B) :
    AnalyticSet (f ⁻¹' (g '' B)) := by
  let S : Set (NatTree × Y) := {p | f p.1 = g p.2} ∩ Prod.snd ⁻¹' B
  have hS : MeasurableSet S :=
    (ClosedSubspaces.measurableSet_eq_of_measurable
      (hf.comp measurable_fst) (hg.comp measurable_snd)).inter (measurable_snd hB)
  have he : Prod.fst '' S = f ⁻¹' (g '' B) :=
    Set.ext fun _ => by simp [S, and_comm, eq_comm]
  exact he ▸ hS.analyticSet_image measurable_fst

/-- An analytic family containing the common complemented-hereditary class is complementably universal. -/
theorem analytic_family_contains_complemented_copy {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] {g : Y → BanachCode} {B : Set Y}
    (hg : Measurable g) (hB : MeasurableSet B)
    (hA : ∀ X : BanachCode,
      (∀ p : RealBanachSpace → Prop, IsL1StableComplementedProperty p →
        p (RealBanachSpace.of X.val)) → X ∈ g '' B)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ X : BanachCode, X ∈ g '' B ∧ ComplementablyEmbeds E X.val := by
  obtain ⟨Φ, hΦ, hW, hI⟩ := exists_borelReduction E
  have hpre := analyticSet_preimage_banachCode_image hΦ hg hB
  have hsub : {T : NatTree | T.IsWellFounded} ⊆ Φ ⁻¹' (g '' B) :=
    fun T hT => hA (Φ T) fun p hp => hW T hT p hp.1
  have htree : ∃ T, Φ T ∈ g '' B ∧ ¬ T.IsWellFounded := by
    by_contra! h
    have he : Φ ⁻¹' (g '' B) = {T : NatTree | T.IsWellFounded} :=
      subset_antisymm (fun T hT => h T hT) hsub
    exact NatTree.not_analyticSet_wellFounded (he ▸ hpre)
  obtain ⟨T, hT, hwf⟩ := htree
  have hif : T.IsIllFounded := Set.nonempty_iff_ne_empty.mpr hwf
  obtain ⟨i, r, _, hri⟩ := hI T hif
  exact ⟨Φ T, hT, i.toContinuousLinearMap, r, hri⟩

end PaperFormalization
