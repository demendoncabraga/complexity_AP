import PaperFormalization.TreeRoot
import PaperFormalization.SuccessorCoordinates
import PaperFormalization.L1FamilyQuotient

namespace PaperFormalization

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem successorKernelFamily_eq_ker (P : L1 ℕ →L[ℝ] E) :
    successorKernelFamily P =
      (l1CoordinateQuotient (branchKernelSpan (tailOperator P))).toLinearMap.ker := by
  ext x
  rw [mem_successorKernelFamily]
  constructor
  · intro h
    exact lp.ext (funext fun m => (Submodule.Quotient.mk_eq_zero _).mpr (h m))
  · intro h m
    have he : l1CoordinateQuotient (branchKernelSpan (tailOperator P)) x = 0 := h
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg
      (fun y : lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1 => y m) he)

theorem treeRootLine_eq_map (P : L1 ℕ →L[ℝ] E) :
    treeRootLine P = rootCoordinateLine.map (branchKernelSpan P).mkQ := by
  rw [rootCoordinateLine, Submodule.map_span, Set.image_singleton]
  rfl

/-- The ambient quotient by the root line is the ℓ₁ sum of the ambient successor quotients. -/
noncomputable def ambientSuccessorQuotientEquiv (P : L1 ℕ →L[ℝ] E) :
    (TreeQuotient P ⧸ treeRootLine P) ≃ₗᵢ[ℝ] lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1 :=
  (Submodule.quotLIEOfEq _ _ (treeRootLine_eq_map P)).trans
    ((Submodule.quotientQuotientLIEQuotientSup (branchKernelSpan P) rootCoordinateLine).trans
      ((rootQuotientSplitEquiv P).trans
        ((Submodule.quotLIEOfEq _ _ (successorKernelFamily_eq_ker P)).trans
          (l1CoordinateQuotientEquiv (branchKernelSpan (tailOperator P))))))

theorem ambientSuccessorQuotientEquiv_on_node (P : L1 ℕ →L[ℝ] E) (s : List ℕ) :
    ambientSuccessorQuotientEquiv P ((treeRootLine P).mkQ
      ((branchKernelSpan P).mkQ (lp.single 1 s 1))) =
      match s with
      | [] => 0
      | m :: u => lp.single 1 m ((branchKernelSpan (tailOperator P)).mkQ (lp.single 1 u 1)) := by
  change l1CoordinateQuotient (branchKernelSpan (tailOperator P)) (splitRootL1 (lp.single 1 s 1)) = _
  cases s <;> simp [splitRootL1, l1CoordinateQuotient_single, Submodule.mkQ_apply]

/-- The subspace of the sum with each coordinate in its corresponding successor tree space. -/
noncomputable def successorTreeFamily (P : L1 ℕ →L[ℝ] E) (T : NatTree) :
    Submodule ℝ (lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1) :=
  ⨅ m : ℕ, (treeSpace (tailOperator P) (T.successor m)).comap
    (lp.evalₗ (fun _ : ℕ => TreeQuotient (tailOperator P)) 1 m)

theorem mem_successorTreeFamily (P : L1 ℕ →L[ℝ] E) (T : NatTree)
    (x : lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1) :
    x ∈ successorTreeFamily P T ↔ ∀ m, x m ∈ treeSpace (tailOperator P) (T.successor m) := by
  simp [successorTreeFamily, Submodule.mem_iInf]

theorem isClosed_successorTreeFamily (P : L1 ℕ →L[ℝ] E) (T : NatTree) :
    IsClosed (successorTreeFamily P T : Set (lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1)) := by
  have he : (successorTreeFamily P T : Set (lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1)) =
      ⋂ m : ℕ, {x | x m ∈ treeSpace (tailOperator P) (T.successor m)} :=
    Set.ext fun x => by simp [mem_successorTreeFamily]
  rw [he]
  exact isClosed_iInter fun m =>
    (Submodule.isClosed_topologicalClosure _).preimage
      (lp.evalCLM ℝ (fun _ : ℕ => TreeQuotient (tailOperator P)) 1 m).continuous

theorem isClosed_treeSpace_map_root (P : L1 ℕ →L[ℝ] E) (T : NatTree) (hroot : [] ∈ T.val) :
    IsClosed ((treeSpace P T).map (treeRootLine P).mkQ : Set (TreeQuotient P ⧸ treeRootLine P)) := by
  apply (treeRootLine P).isOpenQuotientMap_mkQ.isQuotientMap.isCoinducing.isClosed_preimage.mp
  change IsClosed (((treeSpace P T).map (treeRootLine P).mkQ).comap (treeRootLine P).mkQ :
    Set (TreeQuotient P))
  rw [Submodule.comap_map_mkQ, sup_eq_right.mpr (treeRootLine_le_treeSpace P T hroot)]
  exact Submodule.isClosed_topologicalClosure _

/-- The ambient decomposition sends the image of a tree space onto the corresponding successor sum. -/
theorem map_treeSpace_ambientSuccessor (P : L1 ℕ →L[ℝ] E) (T : NatTree) (hroot : [] ∈ T.val) :
    (treeSpace P T).map ((ambientSuccessorQuotientEquiv P).toLinearMap.comp
      (treeRootLine P).mkQ) = successorTreeFamily P T := by
  let G := ambientSuccessorQuotientEquiv P
  let H := G.toLinearIsometry.toContinuousLinearMap.comp (treeRootLine P).mkQL
  let W := (treeSpace P T).map H.toLinearMap
  have hW : IsClosed (W : Set (lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1)) := by
    change IsClosed ((treeSpace P T).map (G.toLinearMap.comp (treeRootLine P).mkQ) :
      Set (lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1))
    rw [Submodule.map_comp, Submodule.map_coe]
    exact G.toHomeomorph.isClosedMap _ (isClosed_treeSpace_map_root P T hroot)
  have hnode (s : List ℕ) : H ((branchKernelSpan P).mkQ (lp.single 1 s 1)) =
      match s with
      | [] => 0
      | m :: u => lp.single 1 m ((branchKernelSpan (tailOperator P)).mkQ (lp.single 1 u 1)) :=
    ambientSuccessorQuotientEquiv_on_node P s
  change W = successorTreeFamily P T
  refine le_antisymm ?_ ?_
  · change (treeSpace P T).map H.toLinearMap ≤ successorTreeFamily P T
    unfold treeSpace
    refine (Submodule.topologicalClosure_map _ _).trans ?_
    refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_successorTreeFamily P T)
    rw [Submodule.map_span]
    refine Submodule.span_le.mpr fun x hx => ?_
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hx
    change H ((branchKernelSpan P).mkQ (lp.single 1 s 1)) ∈ successorTreeFamily P T
    rw [hnode]
    cases s with
    | nil => exact Submodule.zero_mem _
    | cons k u =>
      apply (mem_successorTreeFamily P T _).mpr
      intro m
      change (lp.single (E := fun _ : ℕ => TreeQuotient (tailOperator P)) 1 k
        ((branchKernelSpan (tailOperator P)).mkQ (lp.single 1 u 1))) m ∈ _
      by_cases he : m = k
      · subst m
        rw [lp.single_apply_self]
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨u, hs, rfl⟩)
      · rw [lp.single_apply_ne _ _ _ he]
        exact Submodule.zero_mem _
  · intro x hx
    refine hW.mem_of_tendsto (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) x) ?_
    refine Filter.Eventually.of_forall fun f => Submodule.sum_mem _ fun m _ => ?_
    let j := lp.singleContinuousLinearMap ℝ (fun _ : ℕ => TreeQuotient (tailOperator P)) 1 m
    have hj : treeSpace (tailOperator P) (T.successor m) ≤ W.comap j.toLinearMap := by
      refine Submodule.topologicalClosure_minimal _ ?_ (hW.preimage j.continuous)
      refine Submodule.span_le.mpr fun y hy => ?_
      obtain ⟨s, hs, rfl⟩ := hy
      change lp.single 1 m ((branchKernelSpan (tailOperator P)).mkQ (lp.single 1 s 1)) ∈ W
      exact Eq.mp (congrArg
        (fun z : lp (fun _ : ℕ => TreeQuotient (tailOperator P)) 1 => z ∈ W)
        (hnode (m :: s))) (Submodule.mem_map.mpr
        ⟨(branchKernelSpan P).mkQ (lp.single 1 (m :: s) 1),
          Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨m :: s, hs, rfl⟩), rfl⟩)
    exact hj ((mem_successorTreeFamily P T x).mp hx m)

/-- A subspace containing a closed kernel has its quotient norm inside the ambient quotient. -/
noncomputable def submoduleQuotientIsometry {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (S U : Submodule ℝ A) [IsClosed (S : Set A)] (h : S ≤ U) :
    (U ⧸ S.comap U.subtype) ≃ₗᵢ[ℝ] U.map S.mkQ := by
  generalize hW : U.map S.mkQ = W
  have hU : W.comap S.mkQ = U := by
    rw [← hW, Submodule.comap_map_mkQ, sup_eq_right.mpr h]
  subst U
  exact quotientPreimageIsometry S W

/-- The root quotient of a nonempty tree space is isometric to its successor sum subspace. -/
noncomputable def treeSpaceRootQuotientEquiv (P : L1 ℕ →L[ℝ] E) (T : NatTree)
    (hroot : [] ∈ T.val) :
    (treeSpace P T ⧸ (treeRootLine P).comap (treeSpace P T).subtype) ≃ₗᵢ[ℝ]
      successorTreeFamily P T :=
  (submoduleQuotientIsometry (treeRootLine P) (treeSpace P T)
    (treeRootLine_le_treeSpace P T hroot)).trans
    (((ambientSuccessorQuotientEquiv P).submoduleMap ((treeSpace P T).map (treeRootLine P).mkQ)).trans
      (LinearIsometryEquiv.ofEq _ _ (by
        rw [← Submodule.map_comp]
        exact map_treeSpace_ambientSuccessor P T hroot)))

/-- The coordinatewise subspace has the norm of the ℓ₁ sum of the successor tree spaces. -/
noncomputable def successorTreeFamilyEquiv (P : L1 ℕ →L[ℝ] E) (T : NatTree) :
    successorTreeFamily P T ≃ₗᵢ[ℝ]
      lp (fun m : ℕ => treeSpace (tailOperator P) (T.successor m)) 1 := by
  let V := successorTreeFamily P T
  let F := fun m : ℕ => treeSpace (tailOperator P) (T.successor m)
  let toSum (x : V) : lp (fun m => F m) 1 :=
    ⟨fun m => ⟨x.val m, (mem_successorTreeFamily P T x.val).mp x.property m⟩,
      memℓp_gen ((lp.memℓp x.val).summable (by simp : 0 < (1 : ℝ≥0∞).toReal))⟩
  let toSubspace (x : lp (fun m => F m) 1) : V :=
    ⟨⟨fun m => (x m).val, memℓp_gen ((lp.memℓp x).summable
        (by simp : 0 < (1 : ℝ≥0∞).toReal))⟩,
      (mem_successorTreeFamily P T _).mpr fun m => (x m).property⟩
  let e : V ≃ₗ[ℝ] lp (fun m => F m) 1 :=
    { toFun := toSum
      invFun := toSubspace
      left_inv := fun x => Subtype.ext (lp.ext rfl)
      right_inv := fun x => lp.ext (funext fun m => Subtype.ext rfl)
      map_add' := fun x y => lp.ext (funext fun m => Subtype.ext rfl)
      map_smul' := fun a x => lp.ext (funext fun m => Subtype.ext rfl) }
  exact { e with
    norm_map' := fun x => by
      change ‖toSum x‖ = ‖x.val‖
      rw [lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) (toSum x),
        lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal) x.val]
      rfl }

/-- The decomposition of a tree space after quotienting out its root line. -/
noncomputable def treeSpaceRootQuotientL1Equiv (P : L1 ℕ →L[ℝ] E) (T : NatTree)
    (hroot : [] ∈ T.val) :
    (treeSpace P T ⧸ (treeRootLine P).comap (treeSpace P T).subtype) ≃ₗᵢ[ℝ]
      lp (fun m : ℕ => treeSpace (tailOperator P) (T.successor m)) 1 :=
  (treeSpaceRootQuotientEquiv P T hroot).trans (successorTreeFamilyEquiv P T)

theorem treeSpace_successor_eq_bot_of_not_mem (P : L1 ℕ →L[ℝ] E) (T : NatTree) (m : ℕ)
    (hm : [m] ∉ T.val) : treeSpace (tailOperator P) (T.successor m) = ⊥ := by
  have h : (T.successor m).val = ∅ := Set.eq_empty_of_forall_notMem fun s hs =>
    hm (T.property [m] (m :: s) (List.prefix_append [m] s) hs)
  rw [treeSpace, h, Set.image_empty, Submodule.span_empty]
  exact (show IsClosed ((⊥ : Submodule ℝ (TreeQuotient (tailOperator P))) :
    Set (TreeQuotient (tailOperator P))) from isClosed_singleton).submodule_topologicalClosure_eq

end PaperFormalization
