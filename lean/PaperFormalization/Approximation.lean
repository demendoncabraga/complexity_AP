import PaperFormalization.Basic

namespace PaperFormalization

theorem HasApproximationProperty.of_complementablyEmbeds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : HasApproximationProperty F) (hEF : ComplementablyEmbeds E F) :
    HasApproximationProperty E := by
  obtain ⟨i, r, hir⟩ := hEF
  intro ε hε K hK
  obtain ⟨A, hA, hAK⟩ := hF (ε / (‖r‖ + 1))
    (div_pos hε (by positivity)) (i '' K) (hK.image i.continuous)
  refine ⟨r.comp (A.comp i), ?_, ?_⟩
  · exact FiniteDimensional.of_injective
      (Submodule.inclusion (show (r.comp (A.comp i)).toLinearMap.range ≤
          (r.toLinearMap.comp A.toLinearMap.range.subtype).range from
        fun y ⟨x, hxy⟩ => ⟨⟨A (i x), ⟨i x, rfl⟩⟩, hxy⟩))
      (Submodule.inclusion_injective _)
  · exact fun x hx => calc
      ‖x - (r.comp (A.comp i)) x‖ = ‖r (i x - A (i x))‖ := by
        rw [map_sub, hir x]
        rfl
      _ ≤ ‖r‖ * ‖i x - A (i x)‖ := r.le_opNorm _
      _ ≤ ‖r‖ * (ε / (‖r‖ + 1)) :=
        mul_le_mul_of_nonneg_left (hAK (i x) ⟨x, hx, rfl⟩) (norm_nonneg r)
      _ ≤ ε := by
        have hpos : 0 < ‖r‖ + 1 := by positivity
        rw [← mul_div_assoc, div_le_iff₀ hpos]
        nlinarith

end PaperFormalization
