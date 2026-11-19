import PaperFormalization.SuccessorOperators

namespace PaperFormalization

open scoped ENNReal

/-- The ℓ₁ sum of the coordinate spaces of the immediate successors. -/
noncomputable abbrev SuccessorCoordinates := lp (fun _ : ℕ => L1 (List ℕ)) 1

/-- Delete the root and group the remaining coordinates by first symbol. -/
noncomputable def splitRootL1 : L1 (List ℕ) →L[ℝ] SuccessorCoordinates :=
  l1Operator (C := 1)
    (fun s => match s with
      | [] => 0
      | m :: u => lp.single 1 m (lp.single 1 u 1))
    zero_le_one (fun s => by cases s <;> simp [lp.norm_single])

theorem norm_splitRootL1_le : ‖splitRootL1‖ ≤ 1 := l1Operator_norm_le _ _ _

/-- Assemble the coordinate blocks as sequences on the non-root nodes. -/
noncomputable def assembleRootL1 : SuccessorCoordinates →L[ℝ] L1 (List ℕ) :=
  (lp.tsumCLM ℝ ℕ (L1 (List ℕ))).comp
    (lp.mapCLM 1 prependL1 zero_le_one (fun _ => norm_l1Push_le _))

theorem norm_assembleRootL1_le : ‖assembleRootL1‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x =>
    (lp.norm_tsum_le _).trans ((ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right (lp.norm_mapCLM_le _ _ _ _) (norm_nonneg x)))

theorem splitRootL1_apply (x : L1 (List ℕ)) (m : ℕ) : splitRootL1 x m = successorL1 m x :=
  DFunLike.congr_fun
    (show (lp.evalCLM ℝ (fun _ : ℕ => L1 (List ℕ)) 1 m).comp splitRootL1 = successorL1 m from
      l1Operator_ext fun s => by
        change splitRootL1 (lp.single 1 s 1) m = successorL1 m (lp.single 1 s 1)
        cases s with
        | nil => simp [splitRootL1, successorL1]
        | cons k u =>
          by_cases h : k = m
          · subst k
            simp [splitRootL1, successorL1]
          · simp [splitRootL1, successorL1, h]) x

@[simp] theorem assembleRootL1_single (m : ℕ) (x : L1 (List ℕ)) :
    assembleRootL1 (lp.single 1 m x) = prependL1 m x := by
  change (∑' k, prependL1 k (lp.single (E := fun _ : ℕ => L1 (List ℕ)) 1 m x k)) = _
  exact (tsum_eq_single m (fun k hk => by rw [lp.single_apply_ne _ _ _ hk, map_zero])).trans
    (by rw [lp.single_apply_self])

@[simp] theorem splitRootL1_prependL1 (m : ℕ) (x : L1 (List ℕ)) :
    splitRootL1 (prependL1 m x) = lp.single 1 m x :=
  DFunLike.congr_fun
    (show splitRootL1.comp (prependL1 m) =
      lp.singleContinuousLinearMap ℝ (fun _ : ℕ => L1 (List ℕ)) 1 m from
        l1Operator_ext fun s => by simp [splitRootL1, prependL1]) x

@[simp] theorem splitRootL1_assembleRootL1 (x : SuccessorCoordinates) :
    splitRootL1 (assembleRootL1 x) = x := by
  have hx := lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) x
  have h := (splitRootL1.comp assembleRootL1).hasSum hx
  exact (by simpa using h :
    HasSum (fun m => lp.single 1 m (x m)) (splitRootL1 (assembleRootL1 x))).unique hx

/-- Retain only the root coordinate. -/
noncomputable def retainRootL1 : L1 (List ℕ) →L[ℝ] L1 (List ℕ) :=
  l1Push fun
    | [] => some []
    | _ :: _ => none

theorem assembleRootL1_splitRootL1 (x : L1 (List ℕ)) :
    assembleRootL1 (splitRootL1 x) = x - retainRootL1 x :=
  DFunLike.congr_fun
    (show assembleRootL1.comp splitRootL1 = ContinuousLinearMap.id ℝ (L1 (List ℕ)) - retainRootL1
      from l1Operator_ext fun s => by
        cases s <;> simp [splitRootL1, prependL1, retainRootL1]) x

theorem retainRootL1_mem_rootCoordinateLine (x : L1 (List ℕ)) :
    retainRootL1 x ∈ rootCoordinateLine := by
  have he : retainRootL1 x = lp.single 1 [] (x []) :=
    DFunLike.congr_fun (show retainRootL1 =
      (lp.singleContinuousLinearMap ℝ (fun _ : List ℕ => ℝ) 1 []).comp
        (lp.evalCLM ℝ (fun _ : List ℕ => ℝ) 1 []) from
      l1Operator_ext fun s => by
        change retainRootL1 (lp.single 1 s 1) = lp.single 1 [] (lp.single (E := fun _ : List ℕ => ℝ) 1 s 1 [])
        cases s <;> simp [retainRootL1, lp.single_apply]) x
  rw [he]
  exact Submodule.mem_span_singleton.mpr ⟨x [], by simp [← lp.single_smul]⟩

section KernelSplit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The common branch kernel enlarged by the root coordinate line. -/
noncomputable def rootAugmentedKernel (P : L1 ℕ →L[ℝ] E) : Submodule ℝ (L1 (List ℕ)) :=
  branchKernelSpan P ⊔ rootCoordinateLine

instance isClosed_rootAugmentedKernel (P : L1 ℕ →L[ℝ] E) :
    IsClosed (rootAugmentedKernel P : Set (L1 (List ℕ))) := by
  let _ : FiniteDimensional ℝ rootCoordinateLine := by unfold rootCoordinateLine; infer_instance
  exact Submodule.isClosed_sup_finiteDimensional _ _ (isClosed_branchKernelSpan P)

/-- The coordinatewise tail kernels in the ℓ₁ sum. -/
noncomputable def successorKernelFamily (P : L1 ℕ →L[ℝ] E) : Submodule ℝ SuccessorCoordinates :=
  ⨅ m : ℕ, (branchKernelSpan (tailOperator P)).comap
    (lp.evalₗ (fun _ : ℕ => L1 (List ℕ)) 1 m)

theorem mem_successorKernelFamily (P : L1 ℕ →L[ℝ] E) (x : SuccessorCoordinates) :
    x ∈ successorKernelFamily P ↔ ∀ m, x m ∈ branchKernelSpan (tailOperator P) := by
  simp [successorKernelFamily, Submodule.mem_iInf]

instance isClosed_successorKernelFamily (P : L1 ℕ →L[ℝ] E) :
    IsClosed (successorKernelFamily P : Set SuccessorCoordinates) := by
  have he : (successorKernelFamily P : Set SuccessorCoordinates) =
      ⋂ m : ℕ, {x : SuccessorCoordinates | x m ∈ branchKernelSpan (tailOperator P)} :=
    Set.ext fun x => by simp [mem_successorKernelFamily]
  rw [he]
  exact isClosed_iInter fun m =>
    (isClosed_branchKernelSpan (tailOperator P)).preimage
      (lp.evalCLM ℝ (fun _ : ℕ => L1 (List ℕ)) 1 m).continuous

theorem splitRootL1_maps_rootAugmentedKernel (P : L1 ℕ →L[ℝ] E) :
    (rootAugmentedKernel P).map splitRootL1.toLinearMap ≤ successorKernelFamily P := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact (mem_successorKernelFamily P _).mpr fun m => by
    have hm : successorL1 m y ∈ (rootAugmentedKernel P).map (successorL1 m).toLinearMap :=
      Submodule.mem_map.mpr ⟨y, hy, rfl⟩
    rw [rootAugmentedKernel, Submodule.map_sup, map_successorL1_branchKernelSpan,
      map_successorL1_rootCoordinateLine, sup_bot_eq] at hm
    exact Eq.mpr (congrArg (fun z : L1 (List ℕ) => z ∈ branchKernelSpan (tailOperator P))
      (splitRootL1_apply y m)) hm

theorem assembleRootL1_maps_successorKernelFamily (P : L1 ℕ →L[ℝ] E) :
    (successorKernelFamily P).map assembleRootL1.toLinearMap ≤ rootAugmentedKernel P := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have hsum : HasSum (fun m => prependL1 m (y m)) (assembleRootL1 y) := by
    simpa only [assembleRootL1_single] using
      assembleRootL1.hasSum (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) y)
  exact (isClosed_rootAugmentedKernel P).mem_of_tendsto hsum
    (Filter.Eventually.of_forall fun t => Submodule.sum_mem _ fun m _ =>
      prependL1_maps_branchKernelSpan P m (Submodule.mem_map.mpr
        ⟨y m, (mem_successorKernelFamily P y).mp hy m, rfl⟩))

/-- Deleting the root sends the augmented branch kernel onto the coordinatewise tail kernels. -/
theorem map_splitRootL1_rootAugmentedKernel (P : L1 ℕ →L[ℝ] E) :
    (rootAugmentedKernel P).map splitRootL1.toLinearMap = successorKernelFamily P :=
  le_antisymm (splitRootL1_maps_rootAugmentedKernel P) fun x hx =>
    Submodule.mem_map.mpr ⟨assembleRootL1 x, assembleRootL1_maps_successorKernelFamily P
      (Submodule.mem_map.mpr ⟨x, hx, rfl⟩), splitRootL1_assembleRootL1 x⟩

theorem map_splitRootL1_rootCoordinateLine :
    rootCoordinateLine.map splitRootL1.toLinearMap = ⊥ := by
  rw [rootCoordinateLine, Submodule.map_span, Set.image_singleton]
  change Submodule.span ℝ {splitRootL1 (lp.single 1 [] 1)} = ⊥
  simp [splitRootL1, Submodule.span_zero_singleton]

theorem map_splitRootL1_branchKernelSpan (P : L1 ℕ →L[ℝ] E) :
    (branchKernelSpan P).map splitRootL1.toLinearMap = successorKernelFamily P := by
  have h := map_splitRootL1_rootAugmentedKernel P
  rw [rootAugmentedKernel, Submodule.map_sup, map_splitRootL1_rootCoordinateLine, sup_bot_eq] at h
  exact h

/-- Deleting the root, descended to the quotient by the augmented branch kernel. -/
noncomputable def splitRootQuotient (P : L1 ℕ →L[ℝ] E) :
    (L1 (List ℕ) ⧸ rootAugmentedKernel P) →L[ℝ] (SuccessorCoordinates ⧸ successorKernelFamily P) :=
  (rootAugmentedKernel P).liftQL ((successorKernelFamily P).mkQL.comp splitRootL1)
    (fun x hx => (Submodule.Quotient.mk_eq_zero _).mpr
      (splitRootL1_maps_rootAugmentedKernel P (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)))

/-- Assemble successor blocks after quotienting by their common kernels. -/
noncomputable def assembleRootQuotient (P : L1 ℕ →L[ℝ] E) :
    (SuccessorCoordinates ⧸ successorKernelFamily P) →L[ℝ] (L1 (List ℕ) ⧸ rootAugmentedKernel P) :=
  (successorKernelFamily P).liftQL ((rootAugmentedKernel P).mkQL.comp assembleRootL1)
    (fun x hx => (Submodule.Quotient.mk_eq_zero _).mpr
      (assembleRootL1_maps_successorKernelFamily P (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)))

theorem assembleRootQuotient_splitRootQuotient (P : L1 ℕ →L[ℝ] E)
    (q : L1 (List ℕ) ⧸ rootAugmentedKernel P) :
    assembleRootQuotient P (splitRootQuotient P q) = q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change Submodule.Quotient.mk (assembleRootL1 (splitRootL1 x)) = Submodule.Quotient.mk x
  rw [assembleRootL1_splitRootL1, Submodule.Quotient.eq]
  have he : x - retainRootL1 x - x = -retainRootL1 x := by abel
  rw [he, neg_mem_iff]
  exact Submodule.mem_sup_right (retainRootL1_mem_rootCoordinateLine x)

theorem splitRootQuotient_assembleRootQuotient (P : L1 ℕ →L[ℝ] E)
    (q : SuccessorCoordinates ⧸ successorKernelFamily P) :
    splitRootQuotient P (assembleRootQuotient P q) = q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change Submodule.Quotient.mk (splitRootL1 (assembleRootL1 x)) = Submodule.Quotient.mk x
  exact congrArg Submodule.Quotient.mk (splitRootL1_assembleRootL1 x)

theorem splitRootQuotient_norm_apply_le (P : L1 ℕ →L[ℝ] E)
    (q : L1 (List ℕ) ⧸ rootAugmentedKernel P) :
    ‖splitRootQuotient P q‖ ≤ ‖q‖ := by
  unfold splitRootQuotient
  apply norm_liftQL_apply_le
  exact fun x => (Submodule.Quotient.norm_mk_le (successorKernelFamily P) (splitRootL1 x)).trans
    (by simpa only [one_mul] using splitRootL1.le_of_opNorm_le norm_splitRootL1_le x)

theorem assembleRootQuotient_norm_apply_le (P : L1 ℕ →L[ℝ] E)
    (q : SuccessorCoordinates ⧸ successorKernelFamily P) :
    ‖assembleRootQuotient P q‖ ≤ ‖q‖ := by
  unfold assembleRootQuotient
  apply norm_liftQL_apply_le
  exact fun x => (Submodule.Quotient.norm_mk_le (rootAugmentedKernel P) (assembleRootL1 x)).trans
    (by simpa only [one_mul] using assembleRootL1.le_of_opNorm_le norm_assembleRootL1_le x)

/-- The ambient root-removal identification, before taking the individual coordinate quotients. -/
noncomputable def rootQuotientSplitEquiv (P : L1 ℕ →L[ℝ] E) :
    (L1 (List ℕ) ⧸ rootAugmentedKernel P) ≃ₗᵢ[ℝ] (SuccessorCoordinates ⧸ successorKernelFamily P) :=
  { (splitRootQuotient P).toLinearMap with
    invFun := assembleRootQuotient P
    left_inv := assembleRootQuotient_splitRootQuotient P
    right_inv := splitRootQuotient_assembleRootQuotient P
    norm_map' := fun q => le_antisymm (splitRootQuotient_norm_apply_le P q) (calc
      ‖q‖ = ‖assembleRootQuotient P (splitRootQuotient P q)‖ :=
        congrArg norm (assembleRootQuotient_splitRootQuotient P q).symm
      _ ≤ ‖splitRootQuotient P q‖ := assembleRootQuotient_norm_apply_le P _) }

end KernelSplit
end PaperFormalization
