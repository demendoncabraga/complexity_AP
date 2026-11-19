import PaperFormalization.BanachProperties
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

namespace PaperFormalization

open Filter Set Topology MeasureTheory
open scoped BigOperators ENNReal NNReal Classical

universe u v

/-- The Radon–Nikodým property for real Banach spaces, using Bochner densities
of absolutely continuous vector measures of finite variation. -/
def HasRadonNikodymProperty (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ (Ω : Type v) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : VectorMeasure Ω E), IsFiniteMeasure ν.variation → ν ≪ᵥ μ.toENNRealVectorMeasure →
      ∃ f : Ω → E, Integrable f μ ∧ μ.withDensityᵥ f = ν

section MapRange

variable {Ω : Type v} [MeasurableSpace Ω]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def mapVectorMeasure (T : E →L[ℝ] F) (ν : VectorMeasure Ω E) : VectorMeasure Ω F :=
  ν.mapRange T.toLinearMap.toAddMonoidHom T.continuous

private theorem variation_mapVectorMeasure_le (T : E →L[ℝ] F) (ν : VectorMeasure Ω E) :
    (mapVectorMeasure T ν).variation ≤ ‖T‖₊ • ν.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  change ‖T (ν s)‖ₑ ≤ (‖T‖₊ • ν.variation) s
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← enorm_eq_nnnorm]
  exact T.le_opENorm_of_le (ν.enorm_measure_le_variation s)

private theorem ac_mapVectorMeasure (T : E →L[ℝ] F) {μ : Measure Ω} {ν : VectorMeasure Ω E}
    (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) :
    mapVectorMeasure T ν ≪ᵥ μ.toENNRealVectorMeasure := by
  intro s hs
  change T (ν s) = 0
  rw [hν hs, map_zero]

end MapRange

theorem HasRadonNikodymProperty.of_complementablyEmbeds {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hF : HasRadonNikodymProperty.{u,v} F) (hEF : ComplementablyEmbeds E F) :
    HasRadonNikodymProperty.{u,v} E := by
  obtain ⟨I, R, hRI⟩ := hEF
  intro Ω _ μ _ ν hfin hν
  let V := mapVectorMeasure I ν
  have hV : IsFiniteMeasure V.variation :=
    isFiniteMeasure_of_le _ (variation_mapVectorMeasure_le I ν)
  obtain ⟨f, hfi, hfd⟩ := hF Ω μ V hV (ac_mapVectorMeasure I hν)
  refine ⟨fun x => R (f x), R.integrable_comp hfi, ?_⟩
  apply VectorMeasure.ext
  intro s hs
  rw [withDensityᵥ_apply (R.integrable_comp hfi) hs]
  change (∫ x in s, R (f x) ∂μ) = ν s
  rw [R.integral_comp_comm hfi.integrableOn, ← withDensityᵥ_apply hfi hs, hfd]
  exact hRI _

section L1Sum

variable {ι : Type u} (E : ι → Type u) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]
  {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}

private noncomputable def singleMap (i : ι) : E i →L[ℝ] lp E 1 :=
  lp.singleContinuousLinearMap ℝ E 1 i

private theorem norm_l1_finite_sum (s : Finset ι) (x : ∀ i, E i) :
    ‖∑ i ∈ s, singleMap E i (x i)‖ = ∑ i ∈ s, ‖x i‖ := by
  simpa only [singleMap, lp.singleContinuousLinearMap_apply, ENNReal.toReal_one,
    Real.rpow_one] using lp.norm_sum_single (p := 1) (by simp) x s

private theorem norm_l1_finite_truncation_le (s : Finset ι) (x : lp E 1) :
    ‖∑ i ∈ s, singleMap E i (x i)‖ ≤ ‖x‖ := by
  rw [norm_l1_finite_sum]
  have h := lp.hasSum_norm (p := 1) (by simp) x
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact (h.summable.sum_le_tsum s (fun _ _ => norm_nonneg _)).trans_eq h.tsum_eq

variable [∀ i, CompleteSpace (E i)]

private theorem lp_one_density_norm_bound
    (ν : VectorMeasure Ω (lp E 1)) (f : ∀ i, Ω → E i)
    (hi : ∀ i, Integrable (f i) μ)
    (hfi : ∀ i, μ.withDensityᵥ (f i) = mapVectorMeasure (lp.evalCLM ℝ E 1 i) ν)
    (s : Finset ι) :
    ∑ i ∈ s, ‖((singleMap E i).integrable_comp (hi i)).toL1 (singleMap E i ∘ f i)‖ₑ
      ≤ ν.variation univ := by
  let w (x : Ω) := ∑ i ∈ s, singleMap E i (f i x)
  have hw : Integrable w μ := integrable_finsetSum _ fun i _ => (singleMap E i).integrable_comp (hi i)
  have hvar : (μ.withDensityᵥ w).variation ≤ ν.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro A hA
    rw [withDensityᵥ_apply hw hA]
    have he : (∫ x in A, w x ∂μ) = ∑ i ∈ s, singleMap E i (ν A i) := by
      change (∫ x in A, ∑ i ∈ s, singleMap E i (f i x) ∂μ) = _
      rw [integral_finsetSum s (fun i _ => ((singleMap E i).integrable_comp (hi i)).integrableOn)]
      apply Finset.sum_congr rfl
      intro i _
      rw [(singleMap E i).integral_comp_comm (hi i).integrableOn,
        ← withDensityᵥ_apply (hi i) hA, hfi i]
      rfl
    rw [he]
    have h := ENNReal.ofReal_le_ofReal (norm_l1_finite_truncation_le E s (ν A))
    simp only [ofReal_norm] at h
    exact h.trans (ν.enorm_measure_le_variation A)
  calc
    _ = ∑ i ∈ s, ∫⁻ a, ‖singleMap E i (f i a)‖ₑ ∂μ :=
      Finset.sum_congr rfl fun i _ => Integrable.enorm_toL1 _
    _ = ∫⁻ a, ∑ i ∈ s, ‖singleMap E i (f i a)‖ₑ ∂μ := by
      rw [lintegral_finsetSum' s fun i _ =>
        ((singleMap E i).integrable_comp (hi i)).aestronglyMeasurable.enorm]
    _ = ∫⁻ a, ‖w a‖ₑ ∂μ := by
      apply lintegral_congr
      intro a
      rw [← ofReal_norm, show ‖w a‖ = ∑ i ∈ s, ‖f i a‖ from norm_l1_finite_sum E s _,
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [← ofReal_norm]
      simp only [singleMap, lp.singleContinuousLinearMap_apply,
        lp.norm_single (by simp : (0 : ℝ≥0∞) < 1)]
    _ = (μ.withDensityᵥ w).variation univ := by
      rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ ≤ ν.variation univ := hvar univ

/-- The Radon–Nikodým property is stable under arbitrary ℓ₁ sums. -/
theorem HasRadonNikodymProperty.lp_one (hE : ∀ i, HasRadonNikodymProperty.{u,v} (E i)) :
    HasRadonNikodymProperty.{u,v} (lp E 1) := by
  intro Ω _ μ _ ν hfin hν
  let ev (i : ι) := lp.evalCLM ℝ E 1 i
  let V (i : ι) := mapVectorMeasure (ev i) ν
  have hV (i : ι) : IsFiniteMeasure (V i).variation :=
    isFiniteMeasure_of_le _ (variation_mapVectorMeasure_le (ev i) ν)
  have he (i : ι) := hE i Ω μ (V i) (hV i) (ac_mapVectorMeasure (ev i) hν)
  choose f hfi hf using he
  let W (i : ι) := ((singleMap E i).integrable_comp (hfi i)).toL1 (singleMap E i ∘ f i)
  have hW : Summable W := by
    apply Summable.of_norm
    refine summable_of_sum_le (c := (ν.variation univ).toReal) (fun _ => norm_nonneg _) fun s => ?_
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    simpa only [ofReal_norm] using lp_one_density_norm_bound E ν f hfi hf s
  let g : Ω →₁[μ] lp E 1 := ∑' i, W i
  have hg : Integrable g μ := L1.integrable_coeFn g
  refine ⟨g, hg, ?_⟩
  apply VectorMeasure.ext
  intro s hs
  rw [withDensityᵥ_apply hg hs]
  apply lp.ext
  funext j
  let T := (ev j).compLpL 1 μ
  have hcomp (i : ι) : T (W i) = if i = j then (hfi j).toL1 (f j) else 0 := by
    by_cases hij : i = j
    · subst i
      rw [if_pos rfl]
      apply Lp.ext
      filter_upwards [(ev j).coeFn_compLpL (W j),
        ((singleMap E j).integrable_comp (hfi j)).coeFn_toL1, (hfi j).coeFn_toL1]
        with x hx hW' hf'
      change (W j) x = singleMap E j (f j x) at hW'
      rw [hx, hW', hf']
      change (lp.single 1 j (f j x)) j = f j x
      exact lp.single_apply_self ..
    · rw [if_neg hij]
      apply Lp.ext
      filter_upwards [(ev j).coeFn_compLpL (W i),
        ((singleMap E i).integrable_comp (hfi i)).coeFn_toL1, Lp.coeFn_zero (E := E j) (p := 1) (μ := μ)]
        with x hx hW' h0
      change (W i) x = singleMap E i (f i x) at hW'
      rw [hx, hW', h0]
      change (lp.single 1 i (f i x) : lp E 1) j = 0
      exact lp.single_apply_ne 1 i (f i x) (fun h => hij h.symm)
  have heq : T g = (hfi j).toL1 (f j) := by
    change T (∑' i, W i) = _
    rw [T.map_tsum hW]
    simp [hcomp]
  change ev j (∫ x in s, g x ∂μ) = ν s j
  rw [← (ev j).integral_comp_comm hg.integrableOn, ← (ev j).setIntegral_compLp g hs]
  change (∫ x in s, (T g) x ∂μ) = _
  rw [heq, setIntegral_congr_ae hs ((hfi j).coeFn_toL1.mono fun x h _ => h),
    ← withDensityᵥ_apply (hfi j) hs, hf j]
  rfl

end L1Sum

/-- The Radon–Nikodým property belongs to the manuscript's sum-stable class. -/
theorem radonNikodymProperty_isL1Stable :
    IsL1StableProperty (fun E => HasRadonNikodymProperty.{0,v} E) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y e h
    exact h.of_complementablyEmbeds
      ⟨e.symm.toContinuousLinearMap, e.toContinuousLinearMap, e.apply_symm_apply⟩
  · intro Ω _ μ _ ν _ _
    refine ⟨0, integrable_zero _ _ _, ?_⟩
    exact VectorMeasure.ext fun _ _ => Subsingleton.elim _ _
  · intro Ω _ μ _ ν _ hν
    let η : SignedMeasure Ω := ν
    exact ⟨η.rnDeriv μ, SignedMeasure.integrable_rnDeriv _ _,
      SignedMeasure.withDensityᵥ_rnDeriv_eq η μ hν⟩
  · intro ι F h
    exact HasRadonNikodymProperty.lp_one (fun i => (F i : Type)) h

end PaperFormalization
