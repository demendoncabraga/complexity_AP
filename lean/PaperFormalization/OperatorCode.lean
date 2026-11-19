import PaperFormalization.BorelAssignment
import Mathlib.Analysis.Normed.Operator.Extend

namespace PaperFormalization

open Set Topology
open scoped BigOperators

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A countable test that prescribed values on a sequence respect a common linear bound. -/
def SequenceLinearBound (x : ℕ → E) (y : ℕ → F) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℚ),
    ‖∑ i, (a i : ℝ) • y i‖ ≤ C * ‖∑ i, (a i : ℝ) • x i‖

private theorem SequenceLinearBound.realCoefficients {x : ℕ → E} {y : ℕ → F} {C : ℝ}
    (h : SequenceLinearBound x y C) (n : ℕ) (b : Fin n → ℝ) :
    ‖∑ i, b i • y i‖ ≤ C * ‖∑ i, b i • x i‖ := by
  have hd : DenseRange (fun a : Fin n → ℚ => fun i => (a i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun c => ‖∑ i, c i • y i‖ ≤ C * ‖∑ i, c i • x i‖) b ?_ (h n)
  · apply isClosed_le
    · exact (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const).norm
    · exact continuous_const.mul
        (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const).norm

private theorem linearCombination_eq_sum_initial {G : Type*} [AddCommMonoid G]
    [Module ℝ G] (v : ℕ → G) (a : ℕ →₀ ℝ) {n : ℕ} (hs : a.support ⊆ Finset.range n) :
    Finsupp.linearCombination ℝ v a = ∑ i : Fin n, a i • v i := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Fin.sum_univ_eq_sum_range (fun i => a i • v i)]
  exact Finset.sum_subset hs fun i _ hi => by simp [Finsupp.notMem_support_iff.mp hi]

theorem SequenceLinearBound.exists_operator [CompleteSpace F]
    {x : ℕ → E} {y : ℕ → F} {C : ℝ} (h : SequenceLinearBound x y C) (hx : DenseRange x) :
    ∃ T : E →L[ℝ] F, (∀ i, T (x i) = y i) ∧ ∀ z, ‖T z‖ ≤ C * ‖z‖ := by
  classical
  let f := Finsupp.linearCombination ℝ y
  let e := Finsupp.linearCombination ℝ x
  have hd : DenseRange e := by
    apply hx.mono
    rintro z ⟨i, rfl⟩
    exact ⟨Finsupp.single i 1, by simp [e]⟩
  have hb (a : ℕ →₀ ℝ) : ‖f a‖ ≤ C * ‖e a‖ := by
    let n := a.support.sup id + 1
    have hs : a.support ⊆ Finset.range n := by
      intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    dsimp [f, e]
    rw [linearCombination_eq_sum_initial y a hs, linearCombination_eq_sum_initial x a hs]
    exact h.realCoefficients n (fun i => a i)
  refine ⟨f.extendOfNorm e, fun i => ?_, LinearMap.norm_extendOfNorm_apply_le hd C hb⟩
  have hi := LinearMap.extendOfNorm_eq hd ⟨C, hb⟩ (Finsupp.single i 1)
  simpa [e, f] using hi

theorem SequenceLinearBound.of_operator (T : E →L[ℝ] F) (x : ℕ → E) :
    SequenceLinearBound x (fun i => T (x i)) ‖T‖ := by
  intro n a
  simpa only [map_sum, map_smul] using T.le_opNorm (∑ i : Fin n, (a i : ℝ) • x i)

end

theorem measurableSet_sequenceLinearBound
    {A E F : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    (x : ℕ → A → E) (y : ℕ → A → F) (hx : ∀ i, Measurable (x i))
    (hy : ∀ i, Measurable (y i)) (C : ℝ) :
    MeasurableSet {p | SequenceLinearBound (fun i => x i p) (fun i => y i p) C} := by
  have he : {p | SequenceLinearBound (fun i => x i p) (fun i => y i p) C} =
      ⋂ n : ℕ, ⋂ a : Fin n → ℚ, {p |
        ‖∑ i : Fin n, (a i : ℝ) • y i p‖ ≤ C * ‖∑ i : Fin n, (a i : ℝ) • x i p‖} := by
    ext p
    simp [SequenceLinearBound]
  rw [he]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro a
  apply measurableSet_le
  · exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ => (hy i).const_smul (a i : ℝ)).norm
  · exact measurable_const.mul
      (Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ => (hx i).const_smul (a i : ℝ)).norm

end PaperFormalization
