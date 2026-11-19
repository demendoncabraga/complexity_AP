import PaperFormalization.AmbientSuccessor

namespace PaperFormalization

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance completeSpace_treeSpace (P : L1 ℕ →L[ℝ] E) (T : NatTree) :
    CompleteSpace (treeSpace P T) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem treeSpace_root_finiteDimensional (P : L1 ℕ →L[ℝ] E) (T : NatTree) :
    FiniteDimensional ℝ ((treeRootLine P).comap (treeSpace P T).subtype) ∧
      Module.finrank ℝ ((treeRootLine P).comap (treeSpace P T).subtype) ≤ 1 := by
  let U := treeSpace P T
  let R := (treeRootLine P).comap U.subtype
  let i : R →ₗ[ℝ] treeRootLine P :=
    (U.subtype.comp R.subtype).codRestrict (treeRootLine P) fun x => x.property
  have hi : Function.Injective i := fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : treeRootLine P => (z : TreeQuotient P)) h))
  let _ : FiniteDimensional ℝ (treeRootLine P) := by unfold treeRootLine; infer_instance
  refine ⟨FiniteDimensional.of_injective i hi, ?_⟩
  refine (LinearMap.finrank_le_finrank_of_injective hi).trans ?_
  let r := (branchKernelSpan P).mkQ (lp.single 1 [] 1)
  change Module.finrank ℝ (Submodule.span ℝ {r}) ≤ 1
  by_cases hr : r = 0
  · rw [hr, Submodule.span_zero_singleton, finrank_bot]
    decide
  · exact (finrank_span_singleton (K := ℝ) hr).le

/-- A tree space with a root splits as the product of the root line and the successor sum. -/
theorem treeSpace_equiv_root_prod_successorSum (P : L1 ℕ →L[ℝ] E) (T : NatTree)
    (hroot : [] ∈ T.val) :
    Nonempty ((((treeRootLine P).comap (treeSpace P T).subtype) ×
      lp (fun m : ℕ => treeSpace (tailOperator P) (T.successor m)) 1) ≃L[ℝ] treeSpace P T) := by
  let R := (treeRootLine P).comap (treeSpace P T).subtype
  let _ : FiniteDimensional ℝ R := (treeSpace_root_finiteDimensional P T).1
  obtain ⟨K, hK⟩ := (Submodule.ClosedComplemented.of_finiteDimensional R).exists_isTopCompl
  exact ⟨((ContinuousLinearEquiv.refl ℝ R).prodCongr
    ((treeSpaceRootQuotientL1Equiv P T hroot).symm.toContinuousLinearEquiv.trans
      (Submodule.quotientEquivOfIsTopCompl R K hK))).trans
    (Submodule.prodEquivOfIsTopCompl R K hK)⟩

end PaperFormalization
