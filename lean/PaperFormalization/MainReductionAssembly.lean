import PaperFormalization.WellFoundedReduction
import PaperFormalization.BorelAssignment

namespace PaperFormalization

instance completeSpace_banachCode (X : BanachCode) : CompleteSpace X.val :=
  X.property.completeSpace_coe

theorem IsometricOneComplementablyEmbeds.of_target_isometryEquiv
    {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
    (e : B ≃ₗᵢ[ℝ] C) (h : IsometricOneComplementablyEmbeds A B) :
    IsometricOneComplementablyEmbeds A C := by
  obtain ⟨i, r, hr, hri⟩ := h
  exact IsometricOneComplementablyEmbeds.of_contractive_retract
    (e.toLinearIsometry.toContinuousLinearMap.comp i.toContinuousLinearMap)
    (r.comp e.symm.toLinearIsometry.toContinuousLinearMap)
    (fun x => le_of_eq (by simp))
    (fun x => by simpa using r.le_of_opNorm_le hr (e.symm x))
    (fun x => by simpa using hri x)

/-- The two tree cases give the Borel reduction once the ambient embedding is chosen. -/
theorem exists_borelReduction_of_ambientEmbedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (P : L1 ℕ →L[ℝ] E) (hP : Function.Surjective P)
    (hIso : Isometry (P.toLinearMap.ker.liftQL P le_rfl))
    (v : TreeQuotient P →ₗᵢ[ℝ] BanachAmbient) :
    ∃ Φ : NatTree → BanachCode, Measurable Φ ∧
      (∀ T, T.IsWellFounded → ∀ p : RealBanachSpace → Prop, IsL1StableProperty p →
        p (RealBanachSpace.of (Φ T).val)) ∧
      (∀ T, T.IsIllFounded → IsometricOneComplementablyEmbeds E (Φ T).val) := by
  refine ⟨treeAssignment v, measurable_treeAssignment v, ?_, ?_⟩
  · intro T hT p hp
    exact hp.invariant (treeAssignment_isometry v T).toContinuousLinearEquiv
      (wellFounded_treeSpace_has_property T hT p hp P)
  · intro T hT
    exact IsometricOneComplementablyEmbeds.of_target_isometryEquiv (treeAssignment_isometry v T)
      (illFounded_isometricOneComplementablyEmbeds P T hT hP hIso)

open scoped ENNReal
open TopologicalSpace

/-- A real ℓ₁ space over a countable set of coordinates is separable. -/
theorem separableSpace_l1 (ι : Type*) [Countable ι] : SeparableSpace (L1 ι) := by
  classical
  let unit (i : ι) : L1 ι := lp.single 1 i 1
  let V := Submodule.span ℝ (Set.range unit)
  have hsep : IsSeparable (V : Set (L1 ι)) := (Set.countable_range unit).isSeparable.span
  have hdense : Dense (V : Set (L1 ι)) := fun x =>
    isClosed_closure.mem_of_tendsto (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) x)
      (Filter.Eventually.of_forall fun f => subset_closure
        (Submodule.sum_mem _ fun i _ => by
          have he : lp.single 1 i (x i) = x i • unit i := by
            simpa only [smul_eq_mul, mul_one] using
              lp.single_smul (E := fun _ : ι => ℝ) 1 i (x i) 1
          rw [he]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)))
  exact isSeparable_univ_iff.mp (hdense.closure_eq ▸ hsep.closure)

/-- The ambient quotient in the Borel reduction is a separable Banach space. -/
theorem separableSpace_treeQuotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : L1 ℕ →L[ℝ] E) : SeparableSpace (TreeQuotient P) := by
  let _ := separableSpace_l1 (List ℕ)
  apply isSeparable_univ_iff.mp
  have hr : Set.range (branchKernelSpan P).mkQL = Set.univ :=
    Set.range_eq_univ.mpr (Submodule.Quotient.mk_surjective _)
  exact hr ▸ isSeparable_range (branchKernelSpan P).mkQL.continuous

end PaperFormalization
