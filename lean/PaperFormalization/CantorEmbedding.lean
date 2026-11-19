import PaperFormalization.Basic

namespace PaperFormalization

open TopologicalSpace

/-- The closed dual unit ball with the weak-star topology. -/
abbrev WeakStarUnitBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ↥(WeakDual.toStrongDual (𝕜 := ℝ) (E := E) ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) 1)

instance compactSpace_weakStarUnitBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CompactSpace (WeakStarUnitBall E) :=
  isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) 1)

instance nonempty_weakStarUnitBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Nonempty (WeakStarUnitBall E) :=
  ⟨⟨0, by simp⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weak-star dual unit ball of a separable space has a countable dense sequence. -/
theorem exists_weakStarUnitBall_denseSeq [SeparableSpace E] :
    ∃ f : ℕ → WeakStarUnitBall E, DenseRange f := by
  let _ : MetrizableSpace (WeakStarUnitBall E) :=
    WeakDual.metrizable_of_isCompact ℝ E _ (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) 1)
  let _ : MetricSpace (WeakStarUnitBall E) := TopologicalSpace.metrizableSpaceMetric _
  exact ⟨denseSeq _, denseRange_denseSeq _⟩

/-- Evaluation of a vector on the weak-star dual unit ball. -/
noncomputable def weakStarBallEvaluation (x : E) : C(WeakStarUnitBall E, ℝ) :=
  ⟨fun g => g.val x, (WeakDual.eval_continuous x).comp continuous_subtype_val⟩

/-- Evaluation on the dual unit ball is a linear isometry. -/
noncomputable def weakStarBallLinearIsometry : E →ₗᵢ[ℝ] C(WeakStarUnitBall E, ℝ) where
  toFun := weakStarBallEvaluation
  map_add' x y := ContinuousMap.ext fun g => map_add g.val x y
  map_smul' a x := ContinuousMap.ext fun g => map_smul g.val a x
  norm_map' x := by
    change ‖weakStarBallEvaluation x‖ = ‖x‖
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
      intro g
      have hg : ‖g.val.toStrongDual‖ ≤ 1 := by
        have h := g.property
        change g.val.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℝ E) 1 at h
        simpa only [Metric.mem_closedBall, dist_zero_right] using h
      change ‖g.val.toStrongDual x‖ ≤ ‖x‖
      simpa only [one_mul] using g.val.toStrongDual.le_of_opNorm_le hg x
    · obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℝ x
      let z : WeakStarUnitBall E := ⟨g.toWeakDual, by
        simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
          Metric.mem_closedBall, dist_zero_right] using hg⟩
      have he : weakStarBallEvaluation x z = ‖x‖ := hgx
      have hb := ContinuousMap.norm_coe_le_norm (weakStarBallEvaluation x) z
      simpa only [he, Real.norm_of_nonneg (norm_nonneg x)] using hb

/-- Precomposition by a continuous surjection preserves the supremum norm. -/
noncomputable def continuousMapPrecompIsometry {K L : Type*}
    [TopologicalSpace K] [CompactSpace K] [TopologicalSpace L] [CompactSpace L]
    (f : C(K, L)) (hf : Function.Surjective f) : C(L, ℝ) →ₗᵢ[ℝ] C(K, ℝ) where
  toFun g := g.comp f
  map_add' _ _ := ContinuousMap.ext fun _ => rfl
  map_smul' _ _ := ContinuousMap.ext fun _ => rfl
  norm_map' g := by
    change ‖g.comp f‖ = ‖g‖
    exact le_antisymm
      ((ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun x =>
        ContinuousMap.norm_coe_le_norm g (f x))
      ((ContinuousMap.norm_le _ (norm_nonneg (g.comp f))).mpr fun y =>
        (hf y).elim fun x hx => hx ▸ ContinuousMap.norm_coe_le_norm (g.comp f) x)

theorem exists_cantorSpace_linearIsometry (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SeparableSpace E] : Nonempty (E →ₗᵢ[ℝ] C((ℕ → Bool), ℝ)) := by
  let _ : MetrizableSpace (WeakStarUnitBall E) :=
    WeakDual.metrizable_of_isCompact ℝ E _ (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) 1)
  let _ : MetricSpace (WeakStarUnitBall E) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨f, hfc, hfs⟩ := exists_nat_bool_continuous_surjective_of_compact (WeakStarUnitBall E)
  exact ⟨(continuousMapPrecompIsometry ⟨f, hfc⟩ hfs).comp weakStarBallLinearIsometry⟩

end PaperFormalization
