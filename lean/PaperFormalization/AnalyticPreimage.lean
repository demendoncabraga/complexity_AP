import PaperFormalization.Basic

namespace PaperFormalization

open MeasureTheory Set

/-- Analytic sets in Polish spaces are stable under Borel preimages. -/
theorem analyticSet_preimage_measurable {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {A : Set Y}
    (hf : Measurable f) (hA : AnalyticSet A) : AnalyticSet (f ⁻¹' A) := by
  obtain ⟨Z, t, hp, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hA
  let _ : TopologicalSpace Z := t
  let _ : PolishSpace Z := hp
  let _ : MeasurableSpace Z := borel Z
  let _ : BorelSpace Z := ⟨rfl⟩
  have hgraph : MeasurableSet {p : X × Z | f p.1 = g p.2} :=
    measurableSet_eq_fun (hf.comp measurable_fst) (hg.measurable.comp measurable_snd)
  have he : Prod.fst '' {p : X × Z | f p.1 = g p.2} = f ⁻¹' Set.range g :=
    Set.ext fun x => by simp [eq_comm]
  exact he ▸ hgraph.analyticSet_image measurable_fst

end PaperFormalization
