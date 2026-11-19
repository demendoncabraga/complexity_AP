import PaperFormalization.Approximation
import PaperFormalization.BanachProperties

namespace PaperFormalization

open Filter Set Topology
open scoped BigOperators ENNReal Classical

namespace HasApproximationProperty

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem of_finiteDimensional [FiniteDimensional ℝ E] : HasApproximationProperty E := by
  intro ε hε K hK
  exact ⟨ContinuousLinearMap.id ℝ E, by infer_instance, fun x _ => by simpa using hε.le⟩

theorem of_equiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : HasApproximationProperty E) (e : E ≃L[ℝ] F) : HasApproximationProperty F :=
  h.of_complementablyEmbeds ⟨e.symm.toContinuousLinearMap, e.toContinuousLinearMap, e.apply_symm_apply⟩

section L1Sum

variable {ι : Type*} (G : ι → Type*) [∀ i, NormedAddCommGroup (G i)]

private theorem norm_l1_tail_le (x : lp G 1) (s : Finset ι) :
    ‖x - ∑ i ∈ s, lp.single 1 i (x i)‖ ≤ ‖x‖ := by
  classical
  have he := lp.norm_compl_sum_single (p := 1) (by simp) x s
  simp only [ENNReal.toReal_one, Real.rpow_one] at he
  rw [he]
  exact sub_le_self _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)

private theorem exists_l1_truncation {K : Set (lp G 1)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι, ∀ x ∈ K, ‖x - ∑ i ∈ s, lp.single 1 i (x i)‖ ≤ ε := by
  classical
  obtain ⟨D, _, hD, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 2 by positivity)
  have htails (y : lp G 1) :
      ∀ᶠ s : Finset ι in atTop, ‖y - ∑ i ∈ s, lp.single 1 i (y i)‖ < ε / 2 := by
    have hs : HasSum (fun i => lp.single 1 i (y i)) y := lp.hasSum_single (by simp) y
    have hev := (Metric.tendsto_nhds.mp hs) (ε / 2) (by positivity)
    change ∀ᶠ s : Finset ι in atTop, dist (∑ i ∈ s, lp.single 1 i (y i)) y < ε / 2 at hev
    simpa only [dist_eq_norm, norm_sub_rev] using hev
  have hAll := hD.eventually_all.mpr (fun y _ => htails y)
  obtain ⟨s, hs⟩ := hAll.exists
  refine ⟨s, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨hyD, hxy⟩ := mem_iUnion.mp hy
  have hdiff : ‖x - y‖ < ε / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  have he :
      x - (∑ i ∈ s, lp.single 1 i (x i)) =
        (x - y - ∑ i ∈ s, lp.single 1 i ((x - y) i)) +
          (y - ∑ i ∈ s, lp.single 1 i (y i)) := by
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.single_sub, Finset.sum_sub_distrib]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith [norm_l1_tail_le G (x - y) s, hs y hyD])

variable [∀ i, NormedSpace ℝ (G i)]

/-- The approximation property is stable under arbitrary ℓ₁ sums. -/
theorem lp_one (h : ∀ i, HasApproximationProperty (G i)) : HasApproximationProperty (lp G 1) := by
  classical
  intro ε hε K hK
  obtain ⟨s, hs⟩ := exists_l1_truncation G hK (show 0 < ε / 2 by positivity)
  let δ : ℝ := ε / (2 * (s.card + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let F (i : ι) := lp.evalCLM ℝ G 1 i
  have hA (i : ι) := h i δ hδ (F i '' K) (hK.image (F i).continuous)
  choose A hAf hAK using hA
  let B (i : ι) := (lp.singleContinuousLinearMap ℝ G 1 i).comp ((A i).comp (F i))
  let W (i : ι) := (A i).toLinearMap.range.map (lp.singleContinuousLinearMap ℝ G 1 i).toLinearMap
  let Wsum := s.sup W
  refine ⟨∑ i ∈ s, B i, ?_, ?_⟩
  · have hW (i : ι) : FiniteDimensional ℝ (W i) := by
      have := hAf i
      exact inferInstanceAs (FiniteDimensional ℝ ((A i).toLinearMap.range.map _))
    have : FiniteDimensional ℝ Wsum :=
      (Wsum.fg_iff_finiteDimensional).mp
        (Submodule.fg_finset_sup s W fun i _ => (W i).fg_iff_finiteDimensional.mpr (hW i))
    have hle : (∑ i ∈ s, B i).toLinearMap.range ≤ Wsum := by
      rintro _ ⟨x, rfl⟩
      change (∑ i ∈ s, B i) x ∈ Wsum
      rw [sum_apply]
      exact Wsum.sum_mem fun i hi => (Finset.le_sup hi : W i ≤ Wsum)
        ⟨A i (F i x), ⟨F i x, rfl⟩, rfl⟩
    exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  · intro x hx
    let y := ∑ i ∈ s, lp.single 1 i (x i)
    have hdiff :
        y - (∑ i ∈ s, B i) x = ∑ i ∈ s, lp.single 1 i ((x i) - A i (x i)) := by
      simp only [y, B, F, sum_apply, ContinuousLinearMap.comp_apply,
        lp.singleContinuousLinearMap_apply, lp.single_sub, Finset.sum_sub_distrib]
      rfl
    calc
      ‖x - (∑ i ∈ s, B i) x‖ ≤ ‖x - y‖ + ‖y - (∑ i ∈ s, B i) x‖ := by
        simpa only [dist_eq_norm] using dist_triangle x y ((∑ i ∈ s, B i) x)
      _ ≤ ε / 2 + s.card * δ := by
        apply add_le_add (hs x hx)
        rw [hdiff]
        refine (norm_sum_le _ _).trans ?_
        have hsum : ∑ i ∈ s, ‖lp.single 1 i ((x i) - A i (x i))‖ ≤ ∑ _ ∈ s, δ :=
          Finset.sum_le_sum fun i _ => by
            rw [lp.norm_single (by simp)]
            exact hAK i (F i x) (mem_image_of_mem _ hx)
        simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
      _ ≤ ε := by
        have hprod : (s.card : ℝ) * δ ≤ ε / 2 := by
          dsimp [δ]
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith
        linarith

end L1Sum

end HasApproximationProperty

/-- The approximation property belongs to the manuscript's complemented-hereditary class. -/
theorem approximationProperty_isL1StableComplemented :
    IsL1StableComplementedProperty (fun E => HasApproximationProperty E) :=
  ⟨⟨fun e h => h.of_equiv e, HasApproximationProperty.of_finiteDimensional,
    HasApproximationProperty.of_finiteDimensional,
    fun F => HasApproximationProperty.lp_one (fun i => (F i : Type))⟩,
    fun h hY => hY.of_complementablyEmbeds h⟩

end PaperFormalization
