import PaperFormalization.TreeReduction

namespace PaperFormalization

open Filter Topology

/-- Summing successive approximate lifts gives an exact lift with a geometric norm bound.
The iteration is the one used in Mathlib's proof of the open mapping theorem. -/
theorem exists_preimage_of_geometric_approximation {A E : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : A →L[ℝ] E)
    {c : ℝ} (hc : 0 ≤ c) (hc' : c < 1)
    (hApprox : ∀ y, ∃ x, ‖y - P x‖ ≤ c * ‖y‖ ∧ ‖x‖ ≤ ‖y‖) (y : E) :
    ∃ x, P x = y ∧ ‖x‖ ≤ ‖y‖ / (1 - c) := by
  choose lift hlift using hApprox
  let residual z := z - P (lift z)
  have hres (n : ℕ) : ‖residual^[n] y‖ ≤ c ^ n * ‖y‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
      exact (hlift (residual^[n] y)).1.trans (mul_le_mul_of_nonneg_left ih hc)
  let u n := lift (residual^[n] y)
  have hterms (n : ℕ) : ‖u n‖ ≤ c ^ n * ‖y‖ :=
    (hlift (residual^[n] y)).2.trans (hres n)
  have hgeom : Summable (fun n : ℕ => c ^ n * ‖y‖) :=
    (summable_geometric_of_lt_one hc hc').mul_right _
  have hs : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterms hgeom
  have hpartial (n : ℕ) :
      P (∑ i ∈ Finset.range n, u i) = y - residual^[n] y := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, map_add, ih, Function.iterate_succ_apply', sub_add]
  have hzero : Tendsto (fun n : ℕ => residual^[n] y) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => c ^ n * ‖y‖) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc').mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖y‖) atTop (𝓝 ‖y‖))
    simpa only [sub_zero] using squeeze_zero (fun _ => norm_nonneg _) hres hlim
  refine ⟨∑' n, u n, ?_, ?_⟩
  · have hlim : Tendsto (fun n => P (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (P (∑' n, u n))) :=
      (P.continuous.tendsto _).comp hs.of_norm.hasSum.tendsto_sum_nat
    exact (tendsto_nhds_unique (by simpa only [hpartial] using hlim)
      (tendsto_const_nhds.sub hzero)).trans (sub_zero y)
  · exact calc
      ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n, c ^ n * ‖y‖ := hs.tsum_le_tsum hterms hgeom
      _ = ‖y‖ / (1 - c) := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hc hc', div_eq_mul_inv, mul_comm]

theorem exists_l1_operator_approximation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    ∃ P : L1 ℕ →L[ℝ] E, ‖P‖ ≤ 1 ∧
      ∀ c : ℝ, 0 < c → ∀ y : E, ∃ x, ‖y - P x‖ ≤ c * ‖y‖ ∧ ‖x‖ ≤ ‖y‖ := by
  let _ : Nonempty (Metric.closedBall (0 : E) 1) := ⟨⟨0, by simp⟩⟩
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (Metric.closedBall (0 : E) 1)
  have hvnorm (n : ℕ) : ‖(v n).val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (v n).property
  refine ⟨l1Operator (fun n => (v n).val) zero_le_one hvnorm, l1Operator_norm_le _ _ _, ?_⟩
  intro c hc y
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp⟩
  · have hyNorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    let z : Metric.closedBall (0 : E) 1 :=
      ⟨‖y‖⁻¹ • y, by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
          Real.norm_of_nonneg (norm_nonneg y), inv_mul_cancel₀ hyNorm]⟩
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp hv z c hc
    refine ⟨lp.single 1 n ‖y‖, ?_, ?_⟩
    · have hz : ‖y‖ • z.val = y := by
        change ‖y‖ • (‖y‖⁻¹ • y) = y
        rw [smul_smul, mul_inv_cancel₀ hyNorm, one_smul]
      have hn' : ‖z.val - (v n).val‖ < c := by
        change dist z.val (v n).val < c at hn
        rwa [dist_eq_norm] at hn
      have hdif : y - ‖y‖ • (v n).val = ‖y‖ • (z.val - (v n).val) := by
        rw [smul_sub, hz]
      rw [l1Operator_single, hdif, norm_smul, Real.norm_of_nonneg (norm_nonneg y), mul_comm c]
      exact mul_le_mul_of_nonneg_left hn'.le (norm_nonneg y)
    · simp [lp.norm_single]

theorem isometry_quotientLift_of_almost_minimal_preimages
    {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : A →L[ℝ] E)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hPreimage : ∀ (y : E) (ε : ℝ), 0 < ε → ∃ x, P x = y ∧ ‖x‖ ≤ ‖y‖ + ε) :
    Isometry (P.toLinearMap.ker.liftQL P le_rfl) := by
  apply AddMonoidHomClass.isometry_of_norm
  refine fun q => le_antisymm (norm_liftQL_apply_le _ P le_rfl hP q) ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P.toLinearMap.ker q
  exact le_of_forall_pos_le_add fun ε hε => by
    obtain ⟨x, hPx, hx⟩ := hPreimage (P z) ε hε
    have hq : (Submodule.Quotient.mk x : A ⧸ P.toLinearMap.ker) = Submodule.Quotient.mk z :=
      (Submodule.Quotient.eq _).mpr (by simp [LinearMap.mem_ker, hPx])
    calc
      ‖(Submodule.Quotient.mk z : A ⧸ P.toLinearMap.ker)‖ = ‖(Submodule.Quotient.mk x :
          A ⧸ P.toLinearMap.ker)‖ := congrArg norm hq.symm
      _ ≤ ‖x‖ := Submodule.Quotient.norm_mk_le _ _
      _ ≤ ‖P z‖ + ε := hx

/-- Every separable real Banach space admits a surjective isometric quotient of ℓ₁. -/
theorem exists_l1_isometricQuotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    ∃ P : L1 ℕ →L[ℝ] E, Function.Surjective P ∧
      Isometry (P.toLinearMap.ker.liftQL P le_rfl) := by
  obtain ⟨P, hP, hApprox⟩ := exists_l1_operator_approximation (E := E)
  have hNear (y : E) (ε : ℝ) (hε : 0 < ε) : ∃ x, P x = y ∧ ‖x‖ ≤ ‖y‖ + ε := by
    let bound := ‖y‖ + ε + 1
    let c := ε / bound
    have hb : 0 < bound := by dsimp [bound]; positivity
    have hc : 0 < c := div_pos hε hb
    have hc' : c < 1 := (div_lt_one hb).mpr (by dsimp [bound]; linarith [norm_nonneg y])
    obtain ⟨x, hx, hxNorm⟩ := exists_preimage_of_geometric_approximation P hc.le hc'
      (hApprox c hc) y
    have hmul : (‖y‖ + ε) * c ≤ ε :=
      (mul_le_mul_of_nonneg_right (show ‖y‖ + ε ≤ bound from
        le_add_of_nonneg_right zero_le_one) hc.le).trans_eq (by
          rw [show c = ε / bound from rfl, ← mul_div_assoc, mul_div_cancel_left₀ ε hb.ne'])
    exact ⟨x, hx, hxNorm.trans ((div_le_iff₀ (sub_pos.mpr hc')).mpr (by nlinarith only [hmul]))⟩
  exact ⟨P, fun y => (hNear y 1 zero_lt_one).elim fun x hx => ⟨x, hx.1⟩,
    isometry_quotientLift_of_almost_minimal_preimages P
      (fun x => by simpa only [one_mul] using P.le_of_opNorm_le hP x) hNear⟩

end PaperFormalization
