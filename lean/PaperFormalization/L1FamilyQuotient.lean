import PaperFormalization.L1Quotient

namespace PaperFormalization

open scoped ENNReal

section CoordinateQuotient

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (Z : Submodule ℝ A) [IsClosed (Z : Set A)]

/-- Apply a quotient map in each coordinate of a countable ℓ₁ sum. -/
noncomputable def l1CoordinateQuotient :
    lp (fun _ : ℕ => A) 1 →L[ℝ] lp (fun _ : ℕ => A ⧸ Z) 1 :=
  lp.mapCLM 1 (fun _ => Z.mkQL) zero_le_one fun _ =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x =>
      (Submodule.Quotient.norm_mk_le Z x).trans_eq (one_mul _).symm

theorem norm_l1CoordinateQuotient_le : ‖l1CoordinateQuotient Z‖ ≤ 1 :=
  lp.norm_mapCLM_le _ _ _ _

theorem l1CoordinateQuotient_apply (x : lp (fun _ : ℕ => A) 1) (m : ℕ) :
    l1CoordinateQuotient Z x m = Submodule.Quotient.mk (x m) :=
  rfl

theorem l1CoordinateQuotient_single (m : ℕ) (x : A) :
    l1CoordinateQuotient Z (lp.single 1 m x) =
      lp.single 1 m (Submodule.Quotient.mk x) := by
  refine lp.ext (funext fun n => ?_)
  rw [l1CoordinateQuotient_apply]
  by_cases h : n = m
  · subst n
    simp
  · rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ h]
    rfl

theorem l1CoordinateQuotient_nearPreimages (y : lp (fun _ : ℕ => A ⧸ Z) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x, l1CoordinateQuotient Z x = y ∧ ‖x‖ ≤ ‖y‖ + ε := by
  let error := fun n : ℕ => ε / 2 / 2 ^ n
  have herror (n : ℕ) : 0 < error n := by dsimp [error]; positivity
  choose x hx hxnorm using fun n => Submodule.Quotient.norm_mk_lt (y n) (herror n)
  have hySum : Summable (fun n => ‖y n‖) := by
    simpa using (lp.memℓp y).summable (by simp)
  have hbound : Summable (fun n => ‖y n‖ + error n) := hySum.add (summable_geometric_two' ε)
  have hxSum : Summable (fun n => ‖x n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (hxnorm n).le) hbound
  let v : lp (fun _ : ℕ => A) 1 := ⟨x, memℓp_gen (by simpa using hxSum)⟩
  refine ⟨v, lp.ext (funext hx), ?_⟩
  exact calc
    ‖v‖ = ∑' n, ‖x n‖ := by
      simpa only [ENNReal.toReal_one, Real.rpow_one, div_one] using
        lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) v
    _ ≤ ∑' n, (‖y n‖ + error n) := hxSum.tsum_le_tsum (fun n => (hxnorm n).le) hbound
    _ = (∑' n, ‖y n‖) + ∑' n, error n := hySum.tsum_add (summable_geometric_two' ε)
    _ = ‖y‖ + ε := congrArg₂ (· + ·) (by
      simpa only [ENNReal.toReal_one, Real.rpow_one, div_one] using
        (lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) y).symm) (tsum_geometric_two' ε)

/-- Quotienting the sum by the coordinatewise kernel gives the sum of the quotient spaces. -/
noncomputable def l1CoordinateQuotientEquiv :
    (lp (fun _ : ℕ => A) 1 ⧸ (l1CoordinateQuotient Z).toLinearMap.ker) ≃ₗᵢ[ℝ]
      lp (fun _ : ℕ => A ⧸ Z) 1 := by
  let f := l1CoordinateQuotient Z
  let _ : IsClosed (f.toLinearMap.ker : Set (lp (fun _ : ℕ => A) 1)) := f.isClosed_ker
  let g := f.toLinearMap.ker.liftQL f le_rfl
  have hIso : Isometry g := isometry_quotientLift_of_almost_minimal_preimages f
    (fun x => by simpa only [one_mul] using f.le_of_opNorm_le (norm_l1CoordinateQuotient_le Z) x)
    (l1CoordinateQuotient_nearPreimages Z)
  exact LinearIsometryEquiv.ofSurjective (g.toLinearMap.toLinearIsometry hIso) fun y =>
    (l1CoordinateQuotient_nearPreimages Z y 1 zero_lt_one).elim fun x hx =>
      ⟨Submodule.Quotient.mk x, hx.1⟩

end CoordinateQuotient
end PaperFormalization
