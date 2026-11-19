import PaperFormalization.CantorEmbedding
import PaperFormalization.SuccessorOperators

namespace PaperFormalization

open Set Topology TopologicalSpace
open scoped ENNReal

/-- The weak-star unit ball of ℓ∞ in coordinate form. -/
abbrev DualCube := ℕ → Set.Icc (-1 : ℝ) 1

/-- Interpret bounded coordinates as an element of the normed space ℓ∞. -/
noncomputable def DualCube.toLInfinity (c : DualCube) : lp (fun _ : ℕ => ℝ) ∞ :=
  ⟨fun n => (c n).val, memℓp_infty_iff.mpr ⟨1, by
    rintro _ ⟨i, rfl⟩
    exact abs_le.mpr (c i).property⟩⟩

theorem DualCube.range_toLInfinity :
    range DualCube.toLInfinity = Metric.closedBall (0 : lp (fun _ : ℕ => ℝ) ∞) 1 := by
  ext v
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨c, rfl⟩
    rw [lp.norm_eq_ciSup]
    exact ciSup_le fun n => abs_le.mpr (c n).property
  · intro hv
    let c (n : ℕ) : Set.Icc (-1 : ℝ) 1 :=
      ⟨v n, abs_le.mp ((lp.norm_apply_le_norm ENNReal.top_ne_zero v n).trans hv)⟩
    exact ⟨c, lp.ext rfl⟩

theorem weakStarUnitBall_opNorm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : WeakStarUnitBall E) : ‖f.val.toStrongDual‖ ≤ 1 := by
  simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using f.property

private def unitCoordinate (n : ℕ) : L1 ℕ := lp.single 1 n 1

/-- The coordinates of a weak-star functional on ℓ₁ are its values on the unit vectors. -/
noncomputable def weakStarL1Coordinates (f : WeakStarUnitBall (L1 ℕ)) : DualCube :=
  fun n => ⟨f.val (unitCoordinate n), abs_le.mp (by
    have hb := f.val.toStrongDual.le_of_opNorm_le (weakStarUnitBall_opNorm_le f) (unitCoordinate n)
    simpa [unitCoordinate, lp.norm_single] using hb)⟩

/-- The product topology on the coordinate cube coincides with the weak-star topology. -/
theorem isHomeomorph_weakStarL1Coordinates : IsHomeomorph weakStarL1Coordinates := by
  apply isHomeomorph_iff_continuous_bijective.mpr
  refine ⟨continuous_pi fun n => ((WeakDual.eval_continuous (unitCoordinate n)).comp
    continuous_subtype_val).subtype_mk _, ?_, ?_⟩
  · intro f g h
    apply Subtype.ext
    apply WeakDual.toStrongDual.injective
    exact l1Operator_ext fun i => congrArg Subtype.val (congrFun h i)
  · intro c
    let v (i : ℕ) := (c i).val
    have hv (i : ℕ) : ‖v i‖ ≤ 1 := abs_le.mpr (c i).property
    let g : StrongDual ℝ (L1 ℕ) := l1Operator v zero_le_one hv
    have hg : ‖g‖ ≤ 1 := l1Operator_norm_le v zero_le_one hv
    let f : WeakStarUnitBall (L1 ℕ) :=
      ⟨g.toWeakDual, by simpa only [mem_preimage, StrongDual.toStrongDual_toWeakDual,
        Metric.mem_closedBall, dist_zero_right] using hg⟩
    refine ⟨f, funext fun i => Subtype.ext ?_⟩
    change g (lp.single 1 i 1) = v i
    simp [g]

section Evaluation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem dualEvaluation_bound (d : ℕ → E)
    (hd : closure (range d) = Metric.closedBall 0 1) (f : StrongDual ℝ E) (n : ℕ) :
    ‖f (d n)‖ ≤ ‖f‖ := by
  have hdn : d n ∈ Metric.closedBall (0 : E) 1 := hd ▸ subset_closure (mem_range_self n)
  rw [Metric.mem_closedBall, dist_zero_right] at hdn
  exact (f.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) hdn)

/-- Evaluating at a dense sequence in the unit ball embeds the dual linearly and isometrically. -/
noncomputable def dualEvaluationLinearIsometry (d : ℕ → E)
    (hd : closure (range d) = Metric.closedBall 0 1) :
    StrongDual ℝ E →ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) ∞ where
  toFun f := ⟨fun n => f (d n), memℓp_infty_iff.mpr ⟨‖f‖, by
    rintro _ ⟨n, rfl⟩
    exact dualEvaluation_bound d hd f n⟩⟩
  map_add' f g := lp.ext rfl
  map_smul' a f := lp.ext rfl
  norm_map' f := by
    let F : lp (fun _ : ℕ => ℝ) ∞ :=
      ⟨fun n => f (d n), memℓp_infty_iff.mpr ⟨‖f‖, by
        rintro _ ⟨n, rfl⟩
        exact dualEvaluation_bound d hd f n⟩⟩
    change ‖F‖ = ‖f‖
    apply le_antisymm
    · rw [lp.norm_eq_ciSup]
      exact ciSup_le (dualEvaluation_bound d hd f)
    · apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
      intro x hx
      have hcl : IsClosed {y : E | ‖f y‖ ≤ ‖F‖} :=
        isClosed_le f.continuous.norm continuous_const
      have hr : range d ⊆ {y : E | ‖f y‖ ≤ ‖F‖} := by
        rintro _ ⟨n, rfl⟩
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero F n
      have hmem : x ∈ closure (range d) := by rw [hd, Metric.mem_closedBall, dist_zero_right, hx]
      exact closure_minimal hr hcl hmem

end Evaluation

end PaperFormalization
